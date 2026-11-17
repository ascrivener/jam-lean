import Services.Bootstrap.Acc.Final.StaticsZ
import Services.Bootstrap.AllocStart
import Services.Bootstrap.StartMemZ
import Services.Bootstrap.Decode.HeapCtx
import Services.Bootstrap.Acc.Final.KeepK

/-!
# Accumulate from instruction 5 to 6501, with the statics and the allocator's context

`start_ctx`: as `Acc.start_to_6501` (Y's state at instruction 5, the decodes of t, s and |**i**|), with
`Statics.chainZ` in place of `AccBParams.chain`, so that at 6501 also
- the parameter statics hold ([196616]₂ = 𝖢 = 341, [196696]₈ = 𝖨 = 16);
- the allocator's context holds for picoalloc's start state `sStart` (the analogue of refine's
  `ArgsCtx.args_ctx`): the allocator's words are `sStart`'s (`AllocWords`), the heap pages are
  48 … 51, the stack is writable and nothing below 196608 is;
- the read-only data is Y's (memory below 196608 is unchanged, readable octets stay readable).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Picoalloc Services.Bootstrap.Alloc Services.Bootstrap.Alloc.AfterStart Services.Bootstrap.AllocStart
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Addresses the prologue (38875 → 6429) leaves alone, from 196792 up to the stack, except the
    allocator's written words. -/
theorem c177_alloc (a : Nat) (ha : 196792 ≤ a ∧ a < 206512 ∨ 206520 ≤ a ∧ a < 206824 ∨ 206840 ≤ a ∧ a < 206848) :
    AccBParams.C177 a = true := by
  simp only [AccBParams.C0, AccBParams.C1, AccBParams.C2, AccBParams.C3, AccBParams.C4, AccBParams.C5, AccBParams.C6, AccBParams.C7, AccBParams.C8, AccBParams.C9, AccBParams.C10, AccBParams.C11, AccBParams.C12, AccBParams.C13, AccBParams.C14, AccBParams.C15, AccBParams.C16, AccBParams.C17, AccBParams.C18, AccBParams.C19, AccBParams.C20, AccBParams.C21, AccBParams.C22, AccBParams.C23, AccBParams.C24, AccBParams.C25, AccBParams.C26, AccBParams.C27, AccBParams.C28, AccBParams.C29, AccBParams.C30, AccBParams.C31, AccBParams.C32, AccBParams.C33, AccBParams.C34, AccBParams.C35, AccBParams.C36, AccBParams.C37, AccBParams.C38, AccBParams.C39, AccBParams.C40, AccBParams.C41, AccBParams.C42, AccBParams.C43, AccBParams.C44, AccBParams.C45, AccBParams.C46, AccBParams.C47, AccBParams.C48, AccBParams.C49, AccBParams.C50, AccBParams.C51, AccBParams.C52, AccBParams.C53, AccBParams.C54, AccBParams.C55, AccBParams.C56, AccBParams.C57, AccBParams.C58, AccBParams.C59, AccBParams.C60, AccBParams.C61, AccBParams.C62, AccBParams.C63, AccBParams.C64, AccBParams.C65, AccBParams.C66, AccBParams.C67, AccBParams.C68, AccBParams.C69, AccBParams.C70, AccBParams.C71, AccBParams.C72, AccBParams.C73, AccBParams.C74, AccBParams.C75, AccBParams.C76, AccBParams.C77, AccBParams.C78, AccBParams.C79, AccBParams.C80, AccBParams.C81, AccBParams.C82, AccBParams.C83, AccBParams.C84, AccBParams.C85, AccBParams.C86, AccBParams.C87, AccBParams.C88, AccBParams.C89, AccBParams.C90, AccBParams.C91, AccBParams.C92, AccBParams.C93, AccBParams.C94, AccBParams.C95, AccBParams.C96, AccBParams.C97, AccBParams.C98, AccBParams.C99, AccBParams.C100, AccBParams.C101, AccBParams.C102, AccBParams.C103, AccBParams.C104, AccBParams.C105, AccBParams.C106, AccBParams.C107, AccBParams.C108, AccBParams.C109, AccBParams.C110, AccBParams.C111, AccBParams.C112, AccBParams.C113, AccBParams.C114, AccBParams.C115, AccBParams.C116, AccBParams.C117, AccBParams.C118, AccBParams.C119, AccBParams.C120, AccBParams.C121, AccBParams.C122, AccBParams.C123, AccBParams.C124, AccBParams.C125, AccBParams.C126, AccBParams.C127, AccBParams.C128, AccBParams.C129, AccBParams.C130, AccBParams.C131, AccBParams.C132, AccBParams.C133, AccBParams.C134, AccBParams.C135, AccBParams.C136, AccBParams.C137, AccBParams.C138, AccBParams.C139, AccBParams.C140, AccBParams.C141, AccBParams.C142, AccBParams.C143, AccBParams.C144, AccBParams.C145, AccBParams.C146, AccBParams.C147, AccBParams.C148, AccBParams.C149, AccBParams.C150, AccBParams.C151, AccBParams.C152, AccBParams.C153, AccBParams.C154, AccBParams.C155, AccBParams.C156, AccBParams.C157, AccBParams.C158, AccBParams.C159, AccBParams.C160, AccBParams.C161, AccBParams.C162, AccBParams.C163, AccBParams.C164, AccBParams.C165, AccBParams.C166, AccBParams.C167, AccBParams.C168, AccBParams.C169, AccBParams.C170, AccBParams.C171, AccBParams.C172, AccBParams.C173, AccBParams.C174, AccBParams.C175, AccBParams.C176, AccBParams.C177, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      not_and, Nat.not_lt]
  omega

/-- Addresses accumulate's first 600 steps leave alone, from 196792 up to the stack, except the
    allocator's written words. -/
theorem c38_alloc (a : Nat) (ha : 196792 ≤ a ∧ a < 206512 ∨ 206528 ≤ a ∧ a < 206824) :
    AccPrefixC.C38 a = true := by
  simp only [AccPrefixC.C0, AccPrefixC.C1, AccPrefixC.C2, AccPrefixC.C3, AccPrefixC.C4, AccPrefixC.C5, AccPrefixC.C6, AccPrefixC.C7, AccPrefixC.C8, AccPrefixC.C9, AccPrefixC.C10, AccPrefixC.C11, AccPrefixC.C12, AccPrefixC.C13, AccPrefixC.C14, AccPrefixC.C15, AccPrefixC.C16, AccPrefixC.C17, AccPrefixC.C18, AccPrefixC.C19, AccPrefixC.C20, AccPrefixC.C21, AccPrefixC.C22, AccPrefixC.C23, AccPrefixC.C24, AccPrefixC.C25, AccPrefixC.C26, AccPrefixC.C27, AccPrefixC.C28, AccPrefixC.C29, AccPrefixC.C30, AccPrefixC.C31, AccPrefixC.C32, AccPrefixC.C33, AccPrefixC.C34, AccPrefixC.C35, AccPrefixC.C36, AccPrefixC.C37, AccPrefixC.C38, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      not_and, Nat.not_lt]
  omega

/-- **Accumulate from instruction 5 to the call at 6501, with the statics and the allocator's
    context** (see the module docstring). With ℰ(T) ⌢ ℰ(S) ⌢ ℰ(N) as Y's argument octets, the run
    reaches 6501 with sp = 4278057152 in ω₁, ω₇ = sp + 1568, the saved return address 2³² − 2¹⁶ at
    sp + 1848, the parameter statics, `HeapCtxC` for `sStart`, and the memory below 196608 as Y's. -/
theorem start_ctx (p : ByteArray) (P : Program) [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) (henv : heapBounds env.code = (48, 1044430)) (hpar : env.params = Params.full)
    (μ : Memory) (hμ : Prefix.StartMem μ) (hZ : Prefix.StartMemZ μ)
    (hz : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.read a = 0)
    (T S N LA : Nat) (hT : T < 4294967296) (hS : S < 4294967296) (hN : N < 4294967296)
    (hLA : (Blob.encodeNat T).length + (Blob.encodeNat S).length + (Blob.encodeNat N).length = LA)
    (hmem : μ.readN 4278124544 LA = Blob.encodeNat T ++ Blob.encodeNat S ++ Blob.encodeNat N)
    (hrd : ∀ a, 4278124544 ≤ a → a < 4278124544 + LA → μ.readable a = true) (x : AccCtx) :
    ∃ ω' μ', FreeStepsH p (accContract env) 5 (Prefix.initRegs LA) μ x 6501 ω' μ' x 4936 ∧
      ω'[1] = UInt64.ofNat 4278057152 ∧ ω'[7] = UInt64.ofNat 4278058720 ∧
      μ'.readN 4278059000 8 = Num.encodeLE 8 4294901760 ∧
      μ'.readN 196616 2 = Num.encodeLE 2 341 ∧ μ'.readN 196696 8 = Num.encodeLE 8 16 ∧
      HeapCtxC env.code 1044430 4278050816 4278059008 μ' sStart ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a) ∧ (∀ a, μ.readable a = true → μ'.readable a = true) := by
  have hLA3 : 3 ≤ LA ∧ LA ≤ 15 := by
    obtain ⟨a1, a2⟩ := encodeNat_len_le5 T hT
    obtain ⟨b1, b2⟩ := encodeNat_len_le5 S hS
    obtain ⟨c1, c2⟩ := encodeNat_len_le5 N hN
    omega
  obtain ⟨ω₁0, μ₁0, run1, h38⟩ := prefixC_start p P env henv hpar μ hμ hz LA hLA3 x
  have hb0 := bparams_start μ hμ hz LA _ ω₁0 μ₁0 h38
  obtain ⟨ω₂, μ₂, run2, h, hcC, hcI, h3z⟩ := Statics.chainZ p P env ω₁0 μ₁0 x LA hLA3 ω₁0 μ₁0 hb0
  -- as in `start_to_6501`
  have c177 : ∀ a, 4278059008 ≤ a → a < 4294967296 → AccBParams.C177 a = true := by
    intro a h1 h2
    simp only [AccBParams.C0, AccBParams.C1, AccBParams.C2, AccBParams.C3, AccBParams.C4, AccBParams.C5, AccBParams.C6, AccBParams.C7, AccBParams.C8, AccBParams.C9, AccBParams.C10, AccBParams.C11, AccBParams.C12, AccBParams.C13, AccBParams.C14, AccBParams.C15, AccBParams.C16, AccBParams.C17, AccBParams.C18, AccBParams.C19, AccBParams.C20, AccBParams.C21, AccBParams.C22, AccBParams.C23, AccBParams.C24, AccBParams.C25, AccBParams.C26, AccBParams.C27, AccBParams.C28, AccBParams.C29, AccBParams.C30, AccBParams.C31, AccBParams.C32, AccBParams.C33, AccBParams.C34, AccBParams.C35, AccBParams.C36, AccBParams.C37, AccBParams.C38, AccBParams.C39, AccBParams.C40, AccBParams.C41, AccBParams.C42, AccBParams.C43, AccBParams.C44, AccBParams.C45, AccBParams.C46, AccBParams.C47, AccBParams.C48, AccBParams.C49, AccBParams.C50, AccBParams.C51, AccBParams.C52, AccBParams.C53, AccBParams.C54, AccBParams.C55, AccBParams.C56, AccBParams.C57, AccBParams.C58, AccBParams.C59, AccBParams.C60, AccBParams.C61, AccBParams.C62, AccBParams.C63, AccBParams.C64, AccBParams.C65, AccBParams.C66, AccBParams.C67, AccBParams.C68, AccBParams.C69, AccBParams.C70, AccBParams.C71, AccBParams.C72, AccBParams.C73, AccBParams.C74, AccBParams.C75, AccBParams.C76, AccBParams.C77, AccBParams.C78, AccBParams.C79, AccBParams.C80, AccBParams.C81, AccBParams.C82, AccBParams.C83, AccBParams.C84, AccBParams.C85, AccBParams.C86, AccBParams.C87, AccBParams.C88, AccBParams.C89, AccBParams.C90, AccBParams.C91, AccBParams.C92, AccBParams.C93, AccBParams.C94, AccBParams.C95, AccBParams.C96, AccBParams.C97, AccBParams.C98, AccBParams.C99, AccBParams.C100, AccBParams.C101, AccBParams.C102, AccBParams.C103, AccBParams.C104, AccBParams.C105, AccBParams.C106, AccBParams.C107, AccBParams.C108, AccBParams.C109, AccBParams.C110, AccBParams.C111, AccBParams.C112, AccBParams.C113, AccBParams.C114, AccBParams.C115, AccBParams.C116, AccBParams.C117, AccBParams.C118, AccBParams.C119, AccBParams.C120, AccBParams.C121, AccBParams.C122, AccBParams.C123, AccBParams.C124, AccBParams.C125, AccBParams.C126, AccBParams.C127, AccBParams.C128, AccBParams.C129, AccBParams.C130, AccBParams.C131, AccBParams.C132, AccBParams.C133, AccBParams.C134, AccBParams.C135, AccBParams.C136, AccBParams.C137, AccBParams.C138, AccBParams.C139, AccBParams.C140, AccBParams.C141, AccBParams.C142, AccBParams.C143, AccBParams.C144, AccBParams.C145, AccBParams.C146, AccBParams.C147, AccBParams.C148, AccBParams.C149, AccBParams.C150, AccBParams.C151, AccBParams.C152, AccBParams.C153, AccBParams.C154, AccBParams.C155, AccBParams.C156, AccBParams.C157, AccBParams.C158, AccBParams.C159, AccBParams.C160, AccBParams.C161, AccBParams.C162, AccBParams.C163, AccBParams.C164, AccBParams.C165, AccBParams.C166, AccBParams.C167, AccBParams.C168, AccBParams.C169, AccBParams.C170, AccBParams.C171, AccBParams.C172, AccBParams.C173, AccBParams.C174, AccBParams.C175, AccBParams.C176, AccBParams.C177, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      not_and, Nat.not_lt]
    omega
  have c38 : ∀ a, 4278059008 ≤ a → a < 4294967296 → AccPrefixC.C38 a = true := by
    intro a h1 h2
    simp only [AccPrefixC.C0, AccPrefixC.C1, AccPrefixC.C2, AccPrefixC.C3, AccPrefixC.C4, AccPrefixC.C5, AccPrefixC.C6, AccPrefixC.C7, AccPrefixC.C8, AccPrefixC.C9, AccPrefixC.C10, AccPrefixC.C11, AccPrefixC.C12, AccPrefixC.C13, AccPrefixC.C14, AccPrefixC.C15, AccPrefixC.C16, AccPrefixC.C17, AccPrefixC.C18, AccPrefixC.C19, AccPrefixC.C20, AccPrefixC.C21, AccPrefixC.C22, AccPrefixC.C23, AccPrefixC.C24, AccPrefixC.C25, AccPrefixC.C26, AccPrefixC.C27, AccPrefixC.C28, AccPrefixC.C29, AccPrefixC.C30, AccPrefixC.C31, AccPrefixC.C32, AccPrefixC.C33, AccPrefixC.C34, AccPrefixC.C35, AccPrefixC.C36, AccPrefixC.C37, AccPrefixC.C38, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      not_and, Nat.not_lt]
    omega
  have argfr : ∀ a, 4278124544 ≤ a → a < 4278124544 + LA → μ₂.read a = μ.read a := fun a h1 h2 =>
    (h.fr a (c177 a (by omega) (by omega))).trans (h38.fr a (c38 a (by omega) (by omega)))
  have rdfr : ∀ a, 2147483648 ≤ a → μ₂.readable a = μ.readable a := fun a h1 =>
    (h.rdq a).trans (h38.rdA a h1)
  have wrst : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ₂.writable a = true := fun a h1 h2 => by
    rw [h.wrq a]; exact h38.wrm a (hμ.stack a (by omega) h2)
  obtain ⟨ω', μ', run3, r1, r5, r6, r7, r8, r2, r3, r4, r12, m0, m8, mT, mS, mfr, mrd, mwr⟩ :=
    args_run (p := p) (P := P) (R := accContract env) x ω₂ μ₂ T S N LA hT hS hN hLA h.hreg1 h.hreg7
      (by rw [h.hm_4278058720_8]; rfl) h.hbn_4278058728_8
      (by rw [Memory.readN_congr (fun j hj => argfr _ (by omega) (by omega))]; exact hmem)
      (fun a h1 h2 => by rw [rdfr a (by omega)]; exact hrd a h1 h2)
      (fun a h1 h2 => wrst a (by omega) (by omega)) (fun a h1 h2 => wrst a (by omega) (by omega))
      (fun a h1 h2 => wrst a (by omega) (by omega))
  have c177r : ∀ a, 4278059000 ≤ a → a < 4278059008 → AccBParams.C177 a = true := by
    intro a h1 h2
    simp only [AccBParams.C0, AccBParams.C1, AccBParams.C2, AccBParams.C3, AccBParams.C4, AccBParams.C5, AccBParams.C6, AccBParams.C7, AccBParams.C8, AccBParams.C9, AccBParams.C10, AccBParams.C11, AccBParams.C12, AccBParams.C13, AccBParams.C14, AccBParams.C15, AccBParams.C16, AccBParams.C17, AccBParams.C18, AccBParams.C19, AccBParams.C20, AccBParams.C21, AccBParams.C22, AccBParams.C23, AccBParams.C24, AccBParams.C25, AccBParams.C26, AccBParams.C27, AccBParams.C28, AccBParams.C29, AccBParams.C30, AccBParams.C31, AccBParams.C32, AccBParams.C33, AccBParams.C34, AccBParams.C35, AccBParams.C36, AccBParams.C37, AccBParams.C38, AccBParams.C39, AccBParams.C40, AccBParams.C41, AccBParams.C42, AccBParams.C43, AccBParams.C44, AccBParams.C45, AccBParams.C46, AccBParams.C47, AccBParams.C48, AccBParams.C49, AccBParams.C50, AccBParams.C51, AccBParams.C52, AccBParams.C53, AccBParams.C54, AccBParams.C55, AccBParams.C56, AccBParams.C57, AccBParams.C58, AccBParams.C59, AccBParams.C60, AccBParams.C61, AccBParams.C62, AccBParams.C63, AccBParams.C64, AccBParams.C65, AccBParams.C66, AccBParams.C67, AccBParams.C68, AccBParams.C69, AccBParams.C70, AccBParams.C71, AccBParams.C72, AccBParams.C73, AccBParams.C74, AccBParams.C75, AccBParams.C76, AccBParams.C77, AccBParams.C78, AccBParams.C79, AccBParams.C80, AccBParams.C81, AccBParams.C82, AccBParams.C83, AccBParams.C84, AccBParams.C85, AccBParams.C86, AccBParams.C87, AccBParams.C88, AccBParams.C89, AccBParams.C90, AccBParams.C91, AccBParams.C92, AccBParams.C93, AccBParams.C94, AccBParams.C95, AccBParams.C96, AccBParams.C97, AccBParams.C98, AccBParams.C99, AccBParams.C100, AccBParams.C101, AccBParams.C102, AccBParams.C103, AccBParams.C104, AccBParams.C105, AccBParams.C106, AccBParams.C107, AccBParams.C108, AccBParams.C109, AccBParams.C110, AccBParams.C111, AccBParams.C112, AccBParams.C113, AccBParams.C114, AccBParams.C115, AccBParams.C116, AccBParams.C117, AccBParams.C118, AccBParams.C119, AccBParams.C120, AccBParams.C121, AccBParams.C122, AccBParams.C123, AccBParams.C124, AccBParams.C125, AccBParams.C126, AccBParams.C127, AccBParams.C128, AccBParams.C129, AccBParams.C130, AccBParams.C131, AccBParams.C132, AccBParams.C133, AccBParams.C134, AccBParams.C135, AccBParams.C136, AccBParams.C137, AccBParams.C138, AccBParams.C139, AccBParams.C140, AccBParams.C141, AccBParams.C142, AccBParams.C143, AccBParams.C144, AccBParams.C145, AccBParams.C146, AccBParams.C147, AccBParams.C148, AccBParams.C149, AccBParams.C150, AccBParams.C151, AccBParams.C152, AccBParams.C153, AccBParams.C154, AccBParams.C155, AccBParams.C156, AccBParams.C157, AccBParams.C158, AccBParams.C159, AccBParams.C160, AccBParams.C161, AccBParams.C162, AccBParams.C163, AccBParams.C164, AccBParams.C165, AccBParams.C166, AccBParams.C167, AccBParams.C168, AccBParams.C169, AccBParams.C170, AccBParams.C171, AccBParams.C172, AccBParams.C173, AccBParams.C174, AccBParams.C175, AccBParams.C176, AccBParams.C177, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      not_and, Nat.not_lt]
    omega
  have hra : μ'.readN 4278059000 8 = Num.encodeLE 8 4294901760 := by
    rw [show Num.encodeLE 8 4294901760 = [0, 0, 255, 255, 0, 0, 0, 0] by decide, ← h38.hm_4278059000_8]
    exact PVM.Memory.readN_congr fun j hj => by
      rw [mfr _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)), h.fr _ (c177r _ (by omega) (by omega))]
  -- below the stack: the args decode keeps it
  have lo : ∀ a, a < 4278057024 → μ'.read a = μ₂.read a := fun a ha =>
    mfr a (by omega) (.inl ha) (.inl (by omega)) (.inl (by omega))
  have m2 : ∀ a l (v : List UInt8), a + l ≤ 4278057024 → μ₂.readN a l = v → μ'.readN a l = v := fun a l v hal e => by
    rw [Memory.readN_congr (fun j hj => lo _ (by omega))]; exact e
  -- Y's zeros at the allocator's words the start-up leaves alone
  have zr : ∀ a, (196792 ≤ a ∧ a < 206512 ∨ 206528 ≤ a ∧ a < 206824) → μ'.read a = 0 := fun a ha => by
    rw [lo a (by omega), h.fr a (c177_alloc a (by omega)), h38.fr a (c38_alloc a ha)]
    exact hZ.zero a (by omega) (by omega)
  have e512 := m2 206512 8 _ (by omega) h.hm_206512_8
  have e824 := m2 206824 8 _ (by omega) h.hm_206824_8
  have e832 := m2 206832 8 _ (by omega) h.hm_206832_8
  have e848 := m2 206848 4 _ (by omega) h.hm_206848_4
  have e880 := m2 206880 8 _ (by omega) h.hm_206880_8
  have e888 := m2 206888 4 _ (by omega) h.hm_206888_4
  have e892 := m2 206892 4 _ (by omega) h3z
  have e520 : μ'.readN 206520 8 = [32, 40, 3, 0, 0, 0, 0, 0] := by
    have : μ'.readN 206520 8 = μ₁0.readN 206520 8 :=
      Memory.readN_congr (fun j hj => (lo _ (by omega)).trans (h.fr _ (c177_alloc _ (by omega))))
    rw [this]; exact h38.hm_206520_8
  have e840 : μ'.readN 206840 4 = [6, 0, 0, 0] := by
    have : μ'.readN 206840 4 = μ₁0.readN 206840 4 :=
      Memory.readN_congr (fun j hj => (lo _ (by omega)).trans (h.fr _ (c177_alloc _ (by omega))))
    rw [this]; exact h38.hm_206840_4
  have hw : AllocWords μ' := by
    refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold A0; unfold binCount at hb
      by_cases e1 : b = 2431
      · subst e1; simp only [↓reduceIte]; show rdN μ' 206516 4 = 206880
        rw [rdN4_of (a := 206516) (Memory.read_of_readN e512 4 (by decide)) (Memory.read_of_readN e512 5 (by decide))
          (Memory.read_of_readN e512 6 (by decide)) (Memory.read_of_readN e512 7 (by decide))]; rfl
      · simp only [e1, ↓reduceIte]
        by_cases e0 : b = 2430
        · subst e0; show rdN μ' 206512 4 = 0
          rw [rdN4_of (a := 206512) (Memory.read_of_readN e512 0 (by decide)) (Memory.read_of_readN e512 1 (by decide))
            (Memory.read_of_readN e512 2 (by decide)) (Memory.read_of_readN e512 3 (by decide))]; rfl
        · exact rdN4_zero fun j hj => zr _ (by omega)
    · unfold A0
      by_cases e1 : q = 37
      · subst e1; simp only [↓reduceIte]; show rdN μ' 206824 8 = 2 ^ 63
        unfold rdN; rw [e824]; rfl
      · simp only [e1, ↓reduceIte]; exact rdN8_zero fun j hj => zr _ (by omega)
    · unfold rdN; rw [e832]; rfl
    · unfold rdN; rw [e520]; rfl
    · unfold rdN; rw [e840]; rfl
    · rw [rdN4_of (a := 206880) (Memory.read_of_readN e880 0 (by decide)) (Memory.read_of_readN e880 1 (by decide))
        (Memory.read_of_readN e880 2 (by decide)) (Memory.read_of_readN e880 3 (by decide))]; rfl
    · rw [rdN4_of (a := 206884) (Memory.read_of_readN e880 4 (by decide)) (Memory.read_of_readN e880 5 (by decide))
        (Memory.read_of_readN e880 6 (by decide)) (Memory.read_of_readN e880 7 (by decide))]; rfl
    · unfold rdN; rw [e888]; rfl
    · unfold rdN; rw [e892]; rfl
  have wrq : ∀ a, μ'.writable a = μ₁0.writable a := fun a => by rw [mwr, h.wrq]
  have runA : FreeStepsH p (accContract env) 5 (Prefix.initRegs LA) μ x 6501 ω' μ' x 4936 :=
    ((run1.trans run2).trans run3).mono (by decide)
  have lk := ro_keep0 (accContractK_keepsRO hostCostMax env henv) runA hZ.lowRO
  have hlow : ∀ a, a < 196608 → μ'.read a = μ.read a := fun a ha => (lk a ha).1
  refine ⟨ω', μ', runA, r1, r7, hra,
    m2 _ _ _ (by omega) hcC, m2 _ _ _ (by omega) hcI, ?_, hlow,
    fun a ha => by rw [mrd, h.rdq]; exact h38.rdm a ha⟩
  refine ⟨sStart_wf, hw.rep, sStart_first, ?_, by rw [sStart_base]; omega, by rw [sStart_base]; omega,
    by rw [sStart_allocated]; omega, henv, ⟨51, by omega, by omega, HeapPages.of_eq h38.hhp wrq, by omega,
      by rw [sStart_base, sStart_allocated]; omega⟩, by omega, by omega, fun a h1 h2 => ?_, fun a ha => ?_⟩
  · unfold rdN; rw [show μ'.readN 206848 1 = [μ'.read (206848 + 0)] from rfl, Memory.read_of_readN e848 0 (by decide)]; rfl
  · rw [wrq]; exact h38.wrm a (hμ.stack a (by omega) h2)
  · exact (lk a ha).2.2

end Services.Bootstrap.Acc
