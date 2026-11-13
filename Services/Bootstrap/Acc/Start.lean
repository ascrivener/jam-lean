import Services.Bootstrap.AccPrefixC
import Services.Bootstrap.AccBParams
import Services.Bootstrap.Prefix
import Services.Bootstrap.Acc.Args

/-!
# Bootstrap's accumulate from Y's state to its first argument decode

Ψ_A runs the service from instruction 5 (GP v0.8.0 eq. `accinvocation`), which jumps to the
accumulate entry 6378. From Y's registers for arguments of length `LA` (`Prefix.initRegs`, shared
with refine: the same blob, so the same layout), and a starting memory with the facts
`Prefix.StartMem` lists plus zeros on the stack, the run reaches 38875 after 600 steps
(`AccPrefixC`) and 6429 after 3420 (`AccBParams`), where the slot t is decoded. `start_from_Y` states it
from Y itself (`standardInit`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- **Accumulate's first 600 steps**, from instruction 5 to 38875. -/
theorem prefixC_start (p : ByteArray) (P : Program) [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) (henv : heapBounds env.code = (48, 1044430)) (hpar : env.params = Params.full)
    (μ : Memory) (hμ : Prefix.StartMem μ)
    (hz : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.read a = 0)
    (LA : Nat) (hLA : 3 ≤ LA ∧ LA ≤ 15) (x : AccCtx) :
    ∃ ω' μ', FreeStepsH p (accContract env) 5 (Prefix.initRegs LA) μ x 38875 ω' μ' x 600 ∧
      AccPrefixC.St38 LA (Prefix.initRegs LA) μ ω' μ' := by
  have hst := hμ.stack
  have hhe := hμ.heap
  have rd : ∀ a b, (a, b) ∈ Prefix.baseBytes → μ.read a = b := hμ.bytes
  have h0 : AccPrefixC.St0 LA (Prefix.initRegs LA) μ (Prefix.initRegs LA) μ := by
    refine ⟨by simp [Prefix.initRegs], by simp [Prefix.initRegs], by simp [Prefix.initRegs],
      by simp [Prefix.initRegs], by simp [Prefix.initRegs], by simp [Prefix.initRegs],
      by simp [Prefix.initRegs], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a h1 h2 => hhe a (by omega) (by omega), fun a h1 h2 => hhe a (by omega) (by omega),
      fun a h1 h2 => hst a (by omega) (by omega), fun a h1 h2 => hst a (by omega) (by omega),
      fun a h1 h2 => hst a (by omega) (by omega), fun a h1 h2 => hst a (by omega) (by omega),
      fun a h1 h2 => hst a (by omega) (by omega), fun a h1 h2 => hst a (by omega) (by omega),
      fun a h1 h2 => Memory.readable_of_writable (hhe a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hhe a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hhe a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hhe a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hhe a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)),
      fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)),
      hμ.heapPages, fun _ _ => rfl, fun _ _ => rfl, fun _ h => h, fun _ h => h⟩
    · rw [show μ.readN 206512 4 = [μ.read 206512, μ.read 206513, μ.read 206514, μ.read 206515] from rfl,
        rd 206512 0 (by decide), rd 206513 0 (by decide), rd 206514 0 (by decide), rd 206515 0 (by decide)]
    · rw [show μ.readN 206520 8 = [μ.read 206520, μ.read 206521, μ.read 206522, μ.read 206523,
          μ.read 206524, μ.read 206525, μ.read 206526, μ.read 206527] from rfl,
        rd 206520 0 (by decide), rd 206521 0 (by decide), rd 206522 0 (by decide), rd 206523 0 (by decide),
        rd 206524 0 (by decide), rd 206525 0 (by decide), rd 206526 0 (by decide), rd 206527 0 (by decide)]
    · rw [show μ.readN 206824 8 = [μ.read 206824, μ.read 206825, μ.read 206826, μ.read 206827,
          μ.read 206828, μ.read 206829, μ.read 206830, μ.read 206831] from rfl,
        rd 206824 0 (by decide), rd 206825 0 (by decide), rd 206826 0 (by decide), rd 206827 0 (by decide),
        rd 206828 0 (by decide), rd 206829 0 (by decide), rd 206830 0 (by decide), rd 206831 0 (by decide)]
    · rw [show μ.readN 206832 8 = [μ.read 206832, μ.read 206833, μ.read 206834, μ.read 206835,
          μ.read 206836, μ.read 206837, μ.read 206838, μ.read 206839] from rfl,
        rd 206832 0 (by decide), rd 206833 0 (by decide), rd 206834 0 (by decide), rd 206835 0 (by decide),
        rd 206836 0 (by decide), rd 206837 0 (by decide), rd 206838 0 (by decide), rd 206839 0 (by decide)]
    · rw [show μ.readN 206848 4 = [μ.read 206848, μ.read 206849, μ.read 206850, μ.read 206851] from rfl,
        rd 206848 0 (by decide), rd 206849 0 (by decide), rd 206850 0 (by decide), rd 206851 0 (by decide)]
    · rw [show μ.readN 4278056936 8 = [μ.read 4278056936, μ.read 4278056937, μ.read 4278056938,
          μ.read 4278056939, μ.read 4278056940, μ.read 4278056941, μ.read 4278056942, μ.read 4278056943] from rfl,
        hz 4278056936 (by omega) (by omega), hz 4278056937 (by omega) (by omega), hz 4278056938 (by omega) (by omega),
        hz 4278056939 (by omega) (by omega), hz 4278056940 (by omega) (by omega), hz 4278056941 (by omega) (by omega),
        hz 4278056942 (by omega) (by omega), hz 4278056943 (by omega) (by omega)]
    · rw [show μ.readN 4278056944 8 = [μ.read 4278056944, μ.read 4278056945, μ.read 4278056946,
          μ.read 4278056947, μ.read 4278056948, μ.read 4278056949, μ.read 4278056950, μ.read 4278056951] from rfl,
        hz 4278056944 (by omega) (by omega), hz 4278056945 (by omega) (by omega), hz 4278056946 (by omega) (by omega),
        hz 4278056947 (by omega) (by omega), hz 4278056948 (by omega) (by omega), hz 4278056949 (by omega) (by omega),
        hz 4278056950 (by omega) (by omega), hz 4278056951 (by omega) (by omega)]
  obtain ⟨ω', μ', hrun, h38⟩ := AccPrefixC.chain p P env (Prefix.initRegs LA) μ x henv hpar LA hLA
    (Prefix.initRegs LA) μ h0
  refine ⟨ω', μ', ?_, h38⟩
  rw [show Prefix.initRegs LA = regsNF (Prefix.initRegs LA) [] from rfl] at hrun ⊢
  apply FreeStepsH.step_decode (d_5 (p := p) (P := P))
  · pvm_simp []
  exact hrun

/-- Y's RAM is 0 on the stack, 4278050816 … 4278059007. -/
theorem initialMemory_stack_zero (jb : JamBlob) (a : ByteArray) (hl : Prefix.layoutOk jb = true)
    (ha : a.size ≤ inputSize) :
    ∀ j, 4278050816 ≤ j → j < 4278059008 → (initialMemory jb a).read j = 0 := by
  intro j h1 h2
  simp only [Prefix.layoutOk, Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨⟨hro, hrw⟩, _⟩, _⟩, _⟩, _⟩ := hl
  have hrs : rwStart jb = 196608 := by simp [rwStart, hro, roundZone, zoneSize]
  rw [initialMemory_read jb a j (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
    (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
  rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
    ite_eq_right (by rw [hrs, hrw]; omega), ite_eq_right (by simp only [roStart, zoneSize, hro]; omega)]

/-- **From `AccPrefixC`'s end to `AccBParams`' start**: the state at 38875 has what `AccBParams`
    reads, given the starting memory's facts for what the prefix did not touch. -/
theorem bparams_start (μ : Memory) (hμ : Prefix.StartMem μ)
    (hz : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.read a = 0) (LA : Nat) (ω₀ ω' : Regs) (μ' : Memory)
    (h : AccPrefixC.St38 LA ω₀ μ ω' μ') : AccBParams.St0 LA ω' μ' ω' μ' := by
  have hst := hμ.stack
  have hhe := hμ.heap
  have frd : ∀ a, AccPrefixC.C38 a = true → μ'.read a = μ.read a := h.fr
  have w : ∀ a, μ.writable a = true → μ'.writable a = true := h.wrm
  have r : ∀ a, μ.readable a = true → μ'.readable a = true := h.rdm
  refine ⟨h.hreg1, h.hreg4, h.hreg5, h.hreg6, h.hreg8, ?_, h.hm_206512_8, h.hm_206520_8, h.hm_206824_8,
    h.hm_206832_8, h.hm_206848_4, h.hm_206880_8, h.hm_206928_8, h.hm_206936_8, h.hm_206944_8,
    h.hm_206952_8, h.hm_206960_8, h.hm_206968_8, h.hm_206976_8, h.hm_206984_8, h.hm_206992_8,
    h.hm_207000_8, h.hm_207008_8, h.hm_207016_8, h.hm_207024_8, h.hm_207032_2, h.hm_207044_4,
    h.hm_207048_4, h.hm_4278056752_8, h.hm_4278056760_8, h.hm_4278056776_8, h.hm_4278056784_8,
    h.hm_4278056792_8, ?_, h.hm_4278057112_8, h.hm_4278057120_8, h.hm_4278057128_8, h.hm_4278057144_8,
    h.hbn_4278057136_8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · rw [show μ'.readN 196636 4 = [μ'.read 196636, μ'.read 196637, μ'.read 196638, μ'.read 196639] from rfl,
      frd 196636 (by decide), frd 196637 (by decide), frd 196638 (by decide), frd 196639 (by decide),
      hμ.path 196636 8 (by decide), hμ.path 196637 0 (by decide), hμ.path 196638 0 (by decide),
      hμ.path 196639 0 (by decide)]
  · rw [show μ'.readN 4278057106 6 = [μ'.read 4278057106, μ'.read 4278057107, μ'.read 4278057108,
        μ'.read 4278057109, μ'.read 4278057110, μ'.read 4278057111] from rfl,
      frd 4278057106 (by decide), frd 4278057107 (by decide), frd 4278057108 (by decide),
      frd 4278057109 (by decide), frd 4278057110 (by decide), frd 4278057111 (by decide),
      hz 4278057106 (by omega) (by omega), hz 4278057107 (by omega) (by omega), hz 4278057108 (by omega) (by omega),
      hz 4278057109 (by omega) (by omega), hz 4278057110 (by omega) (by omega), hz 4278057111 (by omega) (by omega)]
  all_goals first
    | exact fun a h1 h2 => w a (hhe a (by omega) (by omega))
    | exact fun a h1 h2 => w a (hst a (by omega) (by omega))
    | exact fun a h1 h2 => r a (Memory.readable_of_writable (hhe a (by omega) (by omega)))
    | exact fun a h1 h2 => r a (Memory.readable_of_writable (hst a (by omega) (by omega)))

/-- **Accumulate's start-up, 3420 steps from Y's state at instruction 5 to 6429**, where the first
    `decodeU32` (of the slot t) is called: `prefixC_start`, `bparams_start` and `AccBParams.chain`. -/
theorem start_to_6429 (p : ByteArray) (P : Program) [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) (henv : heapBounds env.code = (48, 1044430)) (hpar : env.params = Params.full)
    (μ : Memory) (hμ : Prefix.StartMem μ)
    (hz : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.read a = 0)
    (LA : Nat) (hLA : 3 ≤ LA ∧ LA ≤ 15) (x : AccCtx) :
    ∃ ω₁ μ₁ ω' μ', FreeStepsH p (accContract env) 5 (Prefix.initRegs LA) μ x 6429 ω' μ' x 3420 ∧
      AccBParams.St177 LA ω₁ μ₁ ω' μ' := by
  obtain ⟨ω₁, μ₁, run1, h38⟩ := prefixC_start p P env henv hpar μ hμ hz LA hLA x
  obtain ⟨ω', μ', run2, h177⟩ := AccBParams.chain p P env ω₁ μ₁ x LA hLA ω₁ μ₁ (bparams_start μ hμ hz LA _ ω₁ μ₁ h38)
  exact ⟨ω₁, μ₁, ω', μ', run1.trans run2, h177⟩

/-- **Bootstrap's accumulate from Y to its first argument decode (6429), 3420 steps.** For a JAM blob with the deployed
    section sizes (`Prefix.layoutOk`) whose PVM code passes `checkCode` for the code facts used
    (`Code`, `CodeX`, `CodeA`; the vendored blob does), and arguments of 3 … 15 octets (Ψ_A's
    ℰ(t, s, |**i**|) for t, s, |**i**| < 2^32), the gas-free machine runs from Y's state at
    instruction 5 to 6429 under `accContract`, for every accumulate environment with the full-chain
    parameters and every context. -/
theorem start_from_Y (b a : ByteArray) (jb : JamBlob) (hjb : JamBlob.parse? b = some jb)
    (hl : Prefix.layoutOk jb = true) (hc : checkCode jb.code Code.facts = true)
    (hcx : checkCode jb.code CodeX.facts = true) (hca : checkCode jb.code CodeA.facts = true)
    (p : ByteArray) (ω : Regs) (μ : Memory) (hY : standardInit b a = some (p, ω, μ)) (env : AccEnv)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.params = Params.full)
    (ha : 3 ≤ a.size ∧ a.size ≤ 15) (x : AccCtx) :
    ∃ P ω₁ μ₁ ω' μ', HasCode p P ∧ HasCodeX p P ∧ HasCodeA p P ∧
      FreeStepsH p (accContract env) 5 ω μ x 6429 ω' μ' x 3420 ∧
      AccBParams.St177 a.size ω₁ μ₁ ω' μ' := by
  obtain ⟨jb', hv, he⟩ := Option.map_eq_some_iff.1 hY
  have hjb' : jb' = jb ∧ a.size ≤ inputSize := by
    unfold validJamBlob? at hv
    by_cases ha : a.size > inputSize
    · rw [ite_eq_left ha] at hv; cases hv
    · rw [ite_eq_right ha, hjb, Option.bind_some] at hv
      split at hv
      · cases hv
      · cases hv; exact ⟨rfl, by omega⟩
  obtain ⟨rfl, hai⟩ := hjb'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨P, hP⟩ := checkCode_sound hc
  haveI i1 : HasCode jb'.code P := ⟨hP⟩
  haveI i2 : HasCodeX jb'.code P := HasCodeX.of hP hcx
  haveI i3 : HasCodeA jb'.code P := HasCodeA.of hP hca
  rw [Prefix.initRegs_eq]
  obtain ⟨ω₁, μ₁, ω', μ', hrun, h⟩ := start_to_6429 _ P env henv hpar _ (Prefix.startMem_initial _ a hl hai)
    (initialMemory_stack_zero _ a hl hai) a.size ha x
  exact ⟨P, ω₁, μ₁, ω', μ', i1, i2, i3, hrun, h⟩

/-- **Accumulate from instruction 5 to the call at 6501, through the decodes of t, s and |**i**|.**
    With ℰ(T) ⌢ ℰ(S) ⌢ ℰ(N) as the starting memory's LA argument octets, the run (`start_to_6429`,
    then `args_run`) reaches 6501 with T, S, N in ω₅, ω₆, ω₈, T and S stored at sp + 256 and
    sp + 260, and otherwise the state `AccBParams.St177` left, outside the decoders' frame. -/
theorem start_to_6501 (p : ByteArray) (P : Program) [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) (henv : heapBounds env.code = (48, 1044430)) (hpar : env.params = Params.full)
    (μ : Memory) (hμ : Prefix.StartMem μ)
    (hz : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.read a = 0)
    (T S N LA : Nat) (hT : T < 4294967296) (hS : S < 4294967296) (hN : N < 4294967296)
    (hLA : (Blob.encodeNat T).length + (Blob.encodeNat S).length + (Blob.encodeNat N).length = LA)
    (hmem : μ.readN 4278124544 LA = Blob.encodeNat T ++ Blob.encodeNat S ++ Blob.encodeNat N)
    (hrd : ∀ a, 4278124544 ≤ a → a < 4278124544 + LA → μ.readable a = true) (x : AccCtx) :
    ∃ ω₁ μ₁ ω₂ μ₂ ω' μ', FreeStepsH p (accContract env) 5 (Prefix.initRegs LA) μ x 6501 ω' μ' x 4936 ∧
      AccBParams.St177 LA ω₁ μ₁ ω₂ μ₂ ∧
      ω'[1] = UInt64.ofNat 4278057152 ∧ ω'[5] = UInt64.ofNat T ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat 4278058720 ∧ ω'[8] = UInt64.ofNat N ∧
      ω'[2] = ω₂[2] ∧ ω'[3] = ω₂[3] ∧ ω'[4] = ω₂[4] ∧ ω'[12] = ω₂[12] ∧
      μ'.readN 4278058720 8 = Num.encodeLE 8 (4278124544 + LA) ∧ μ'.readN 4278058728 8 = Num.encodeLE 8 0 ∧
      μ'.readN 4278057408 4 = Num.encodeLE 4 T ∧ μ'.readN 4278057412 4 = Num.encodeLE 4 S ∧
      (∀ a, a < 4294967296 → (a < 4278057024 ∨ 4278057152 ≤ a) → (a < 4278058720 ∨ 4278058736 ≤ a) →
        (a < 4278057408 ∨ 4278057416 ≤ a) → μ'.read a = μ₂.read a) ∧
      (∀ a, μ'.readable a = μ₂.readable a) ∧ (∀ a, μ'.writable a = μ₂.writable a) ∧
      μ'.readN 4278059000 8 = Num.encodeLE 8 4294901760 := by
  have hLA3 : 3 ≤ LA ∧ LA ≤ 15 := by
    obtain ⟨a1, a2⟩ := encodeNat_len_le5 T hT
    obtain ⟨b1, b2⟩ := encodeNat_len_le5 S hS
    obtain ⟨c1, c2⟩ := encodeNat_len_le5 N hN
    omega
  obtain ⟨ω₁0, μ₁0, run1, h38⟩ := prefixC_start p P env henv hpar μ hμ hz LA hLA3 x
  have hb0 := bparams_start μ hμ hz LA _ ω₁0 μ₁0 h38
  obtain ⟨ω₂, μ₂, run2, h⟩ := AccBParams.chain p P env ω₁0 μ₁0 x LA hLA3 ω₁0 μ₁0 hb0
  -- above the stack, nothing was written: both frames hold there
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
  -- the return address Y left in ω₀ (2³² − 2¹⁶), saved at sp + 1848 by accumulate's prologue
  have c177r : ∀ a, 4278059000 ≤ a → a < 4278059008 → AccBParams.C177 a = true := by
    intro a h1 h2
    simp only [AccBParams.C0, AccBParams.C1, AccBParams.C2, AccBParams.C3, AccBParams.C4, AccBParams.C5, AccBParams.C6, AccBParams.C7, AccBParams.C8, AccBParams.C9, AccBParams.C10, AccBParams.C11, AccBParams.C12, AccBParams.C13, AccBParams.C14, AccBParams.C15, AccBParams.C16, AccBParams.C17, AccBParams.C18, AccBParams.C19, AccBParams.C20, AccBParams.C21, AccBParams.C22, AccBParams.C23, AccBParams.C24, AccBParams.C25, AccBParams.C26, AccBParams.C27, AccBParams.C28, AccBParams.C29, AccBParams.C30, AccBParams.C31, AccBParams.C32, AccBParams.C33, AccBParams.C34, AccBParams.C35, AccBParams.C36, AccBParams.C37, AccBParams.C38, AccBParams.C39, AccBParams.C40, AccBParams.C41, AccBParams.C42, AccBParams.C43, AccBParams.C44, AccBParams.C45, AccBParams.C46, AccBParams.C47, AccBParams.C48, AccBParams.C49, AccBParams.C50, AccBParams.C51, AccBParams.C52, AccBParams.C53, AccBParams.C54, AccBParams.C55, AccBParams.C56, AccBParams.C57, AccBParams.C58, AccBParams.C59, AccBParams.C60, AccBParams.C61, AccBParams.C62, AccBParams.C63, AccBParams.C64, AccBParams.C65, AccBParams.C66, AccBParams.C67, AccBParams.C68, AccBParams.C69, AccBParams.C70, AccBParams.C71, AccBParams.C72, AccBParams.C73, AccBParams.C74, AccBParams.C75, AccBParams.C76, AccBParams.C77, AccBParams.C78, AccBParams.C79, AccBParams.C80, AccBParams.C81, AccBParams.C82, AccBParams.C83, AccBParams.C84, AccBParams.C85, AccBParams.C86, AccBParams.C87, AccBParams.C88, AccBParams.C89, AccBParams.C90, AccBParams.C91, AccBParams.C92, AccBParams.C93, AccBParams.C94, AccBParams.C95, AccBParams.C96, AccBParams.C97, AccBParams.C98, AccBParams.C99, AccBParams.C100, AccBParams.C101, AccBParams.C102, AccBParams.C103, AccBParams.C104, AccBParams.C105, AccBParams.C106, AccBParams.C107, AccBParams.C108, AccBParams.C109, AccBParams.C110, AccBParams.C111, AccBParams.C112, AccBParams.C113, AccBParams.C114, AccBParams.C115, AccBParams.C116, AccBParams.C117, AccBParams.C118, AccBParams.C119, AccBParams.C120, AccBParams.C121, AccBParams.C122, AccBParams.C123, AccBParams.C124, AccBParams.C125, AccBParams.C126, AccBParams.C127, AccBParams.C128, AccBParams.C129, AccBParams.C130, AccBParams.C131, AccBParams.C132, AccBParams.C133, AccBParams.C134, AccBParams.C135, AccBParams.C136, AccBParams.C137, AccBParams.C138, AccBParams.C139, AccBParams.C140, AccBParams.C141, AccBParams.C142, AccBParams.C143, AccBParams.C144, AccBParams.C145, AccBParams.C146, AccBParams.C147, AccBParams.C148, AccBParams.C149, AccBParams.C150, AccBParams.C151, AccBParams.C152, AccBParams.C153, AccBParams.C154, AccBParams.C155, AccBParams.C156, AccBParams.C157, AccBParams.C158, AccBParams.C159, AccBParams.C160, AccBParams.C161, AccBParams.C162, AccBParams.C163, AccBParams.C164, AccBParams.C165, AccBParams.C166, AccBParams.C167, AccBParams.C168, AccBParams.C169, AccBParams.C170, AccBParams.C171, AccBParams.C172, AccBParams.C173, AccBParams.C174, AccBParams.C175, AccBParams.C176, AccBParams.C177, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      not_and, Nat.not_lt]
    omega
  have hra : μ'.readN 4278059000 8 = Num.encodeLE 8 4294901760 := by
    rw [show Num.encodeLE 8 4294901760 = [0, 0, 255, 255, 0, 0, 0, 0] by decide, ← h38.hm_4278059000_8]
    exact PVM.Memory.readN_congr fun j hj => by
      rw [mfr _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)), h.fr _ (c177r _ (by omega) (by omega))]
  exact ⟨ω₁0, μ₁0, ω₂, μ₂, ω', μ', ((run1.trans run2).trans run3).mono (by decide), h, r1, r5, r6, r7, r8,
    r2, r3, r4, r12, m0, m8, mT, mS, mfr, mrd, mwr, hra⟩
end Services.Bootstrap.Acc
