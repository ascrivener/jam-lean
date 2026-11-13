import JAM.Theorems.KeepRO
import JAM.Theorems.HostGas

/-!
# Gas-free runs keep what is not writable, for any contract; the accumulate host calls

`KeepsRO R lo hi`: every continuing host step of R changes no page outside lo … hi and no octet that
is not writable. `FreeStepsH.keepRO_of`: a gas-free run under such an R keeps every page outside
lo … hi and every octet on such a page that is not writable (GP §A.4: a step that continues writes
only indices in 𝕍*_μ). This is the contract-generic form of `FreeStepsH.keepRO` (refine).

`accHostFn_keep`: every accumulate host call that continues (GP v0.8.0 Appendix B) keeps them, with
the heap's 48 … pb: `grow_heap` changes only heap pages; `fetch`, `lookup`, `read` and `info` write
through `writeValue`, which checks writability; the others leave the memory (`*_mem`).
-/

namespace JAM
open PVM

/-- With a body that leaves the memory alone, `charged` leaves it. -/
theorem charged_mem {X : Type} (g gas : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X) (hb : ∀ o, (body o).mem = o.mem) :
    (charged g gas ω μ x body).mem = μ := by
  unfold charged
  split
  · rfl
  · rw [hb]

/-- Close `∀ o, (body o).mem = o.mem` by splitting every `if` and `match` in the body. -/
macro "mem_body" : tactic =>
  `(tactic| (intro o; first | rfl | ((try dsimp only) <;> (repeat' split) <;>
    (try simp only [AccHost.r7, AccHost.panic, AccHost.updX, AccHost.onSelf]) <;> rfl)))

namespace AccHost

theorem bless_mem (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (bless env gas ω μ c).mem = μ := by
  unfold bless charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem assign_mem (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (assign env gas ω μ c).mem = μ := by
  unfold assign charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem designate_mem (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (designate env gas ω μ c).mem = μ := by
  unfold designate charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem new_mem (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (new env gas ω μ c).mem = μ := by
  unfold new charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem transfer_mem (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (transfer env gas ω μ c).mem = μ := by
  unfold transfer charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem eject_mem (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (eject env gas ω μ c).mem = μ := by
  unfold eject charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem solicit_mem (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (solicit env gas ω μ c).mem = μ := by
  unfold solicit charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem forget_mem (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (forget env gas ω μ c).mem = μ := by
  unfold forget charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem checkpoint_mem (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (checkpoint gas ω μ c).mem = μ := by
  unfold checkpoint charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem upgrade_mem (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (upgrade gas ω μ c).mem = μ := by
  unfold upgrade charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem query_mem (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (query gas ω μ c).mem = μ := by
  unfold query charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem yield_mem (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (yield gas ω μ c).mem = μ := by
  unfold yield charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem provide_mem (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (provide gas ω μ c).mem = μ := by
  unfold provide charge; exact charged_mem _ _ _ _ _ _ (by mem_body)

end AccHost

theorem hostWrite_mem (gas : Nat) (ω : Regs) (μ : Memory) (s : ServiceAccount) :
    (hostWrite gas ω μ s).mem = μ := by
  unfold hostWrite; exact charged_mem _ _ _ _ _ _ (by mem_body)

theorem hostGas_mem {X} (gas : Nat) (ω : Regs) (μ : Memory) (x : X) : (hostGas gas ω μ x).mem = μ := by
  unfold hostGas; first | rfl | exact charged_mem _ _ _ _ _ _ (by mem_body)

/-- `writeValue` that continues keeps the pages and every octet that is not writable, for any value. -/
theorem writeValue_keep' {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8))) (o f z : Nat)
    (hs : (writeValue out v o f z).status = .cont) :
    (writeValue out v o f z).mem.pages = out.mem.pages ∧
      ∀ b, b < two32 → out.mem.writable b = false → (writeValue out v o f z).mem.read b = out.mem.read b := by
  cases v with
  | error e => unfold writeValue at hs; simp at hs
  | ok v => exact writeValue_keep out v o f z hs

/-- A charged `writeValue` that continues keeps the pages and every octet that is not writable. -/
theorem charged_wv_keep {X : Type} (g gas : Nat) (ω : Regs) (μ : Memory) (x : X)
    (v : Except Unit (Option (List UInt8))) (o f z : Nat)
    (hs : (charged g gas ω μ x fun out => writeValue out v o f z).status = .cont) :
    (charged g gas ω μ x fun out => writeValue out v o f z).mem.pages = μ.pages ∧
      ∀ b, b < two32 → μ.writable b = false →
        (charged g gas ω μ x fun out => writeValue out v o f z).mem.read b = μ.read b := by
  unfold charged at hs ⊢
  split at hs
  · simp at hs
  · rw [if_neg (by assumption)]
    exact writeValue_keep' _ v o f z hs

/-- **An accumulate host call that continues keeps what is not writable**: no page outside the heap's
    48 … pb changes (`grow_heap` changes only heap pages), and no octet that is not writable changes
    (the reads write through `writeValue`, which checks writability; the others leave the memory). -/
theorem accHostFn_keep (env : AccEnv) {pb : Nat} (hbd : heapBounds env.code = (48, pb)) (h : Nat) (g : UInt64)
    (ω : Regs) (μ : Memory) (c : AccCtx) (hs : (accHostFn env h g ω μ c).status = .cont) :
    (∀ q, (q < 48 ∨ pb ≤ q) → (accHostFn env h g ω μ c).mem.pages.get? q = μ.pages.get? q) ∧
      ∀ b, b < two32 → μ.writable b = false → (accHostFn env h g ω μ c).mem.read b = μ.read b := by
  have same : ∀ o : HostOut AccCtx, o.mem = μ →
      (∀ q, (q < 48 ∨ pb ≤ q) → o.mem.pages.get? q = μ.pages.get? q) ∧
        ∀ b, b < two32 → μ.writable b = false → o.mem.read b = μ.read b :=
    fun o e => by rw [e]; exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  have wv : ∀ {Y : Type} (o : HostOut Y), o.status = .cont → (o.mem.pages = μ.pages ∧
      ∀ b, b < two32 → μ.writable b = false → o.mem.read b = μ.read b) →
      (∀ q, (q < 48 ∨ pb ≤ q) → o.mem.pages.get? q = μ.pages.get? q) ∧
        ∀ b, b < two32 → μ.writable b = false → o.mem.read b = μ.read b :=
    fun o _ ⟨e, k⟩ => ⟨fun q _ => by rw [e], k⟩
  simp only [accHostFn] at hs ⊢
  generalize g.toNat = gn at hs ⊢
  unfold AccHost.dispatch at hs ⊢
  split
  · exact same _ (hostGas_mem _ _ _ _)
  · simp only [hostGrowHeap, growHeapCore, hbd] at hs ⊢
    generalize hC : List.countP (fun k => μ.pages.get? (48 + k) == some Access.write) (List.range (pb - 48)) = C
      at hs ⊢
    have hCle : C ≤ pb - 48 := by
      rw [← hC]; exact Nat.le_trans List.countP_le_length (by simp)
    by_cases c1 : reg ω 7 ≤ 48 + C ∨ reg ω 7 > pb
    · rw [if_pos c1] at hs ⊢
      exact ⟨fun q hq => Memory.setPages_get_off _ _ _ _ _ (by dsimp only; omega), fun b _ _ => rfl⟩
    · rw [if_neg c1] at hs ⊢
      by_cases c2 : gn < Constants.CgasGeminiconst + (reg ω 7 - (48 + C)) * Constants.CgasGeminilinear
      · rw [if_pos c2] at hs; simp at hs
      · rw [if_neg c2]
        exact ⟨fun q hq => Memory.setPages_get_off _ _ _ _ _ (by dsimp only; omega), fun b _ _ => rfl⟩
  · simp only [hostFetch] at hs ⊢; exact wv _ hs (charged_wv_keep _ _ _ _ _ _ _ _ _ hs)
  · simp only [hostLookup] at hs ⊢; exact wv _ hs (charged_wv_keep _ _ _ _ _ _ _ _ _ hs)
  · simp only [hostRead] at hs ⊢; exact wv _ hs (charged_wv_keep _ _ _ _ _ _ _ _ _ hs)
  · exact same _ (by simp only [AccHost.onSelf]; exact hostWrite_mem _ _ _ _)
  · simp only [hostInfo] at hs ⊢; exact wv _ hs (charged_wv_keep _ _ _ _ _ _ _ _ _ hs)
  · exact same _ (AccHost.bless_mem _ _ _ _ _)
  · exact same _ (AccHost.assign_mem _ _ _ _ _)
  · exact same _ (AccHost.designate_mem _ _ _ _ _)
  · exact same _ (AccHost.checkpoint_mem _ _ _ _)
  · exact same _ (AccHost.new_mem _ _ _ _ _)
  · exact same _ (AccHost.upgrade_mem _ _ _ _)
  · exact same _ (AccHost.transfer_mem _ _ _ _ _)
  · exact same _ (AccHost.eject_mem _ _ _ _ _)
  · exact same _ (AccHost.query_mem _ _ _ _)
  · exact same _ (AccHost.solicit_mem _ _ _ _ _)
  · exact same _ (AccHost.forget_mem _ _ _ _ _)
  · exact same _ (AccHost.yield_mem _ _ _ _)
  · exact same _ (AccHost.provide_mem _ _ _ _)
  · exact same _ rfl

/-- **A contract keeps what is not writable off [lo, hi)**: every continuing host step changes no page
    outside lo … hi and no octet that is not writable. -/
def KeepsRO {X : Type} (R : HostRel X) (lo hi : Nat) : Prop :=
  ∀ h ω μ x ω' μ' x', R h ω μ x .cont ω' μ' x' →
    (∀ q, (q < lo ∨ hi ≤ q) → μ'.pages.get? q = μ.pages.get? q) ∧
      ∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b

/-- **A gas-free run under a contract that keeps what is not writable keeps it**: every page outside
    lo … hi keeps its access, and every octet on such a page that is not writable keeps its value
    (contract-generic; `FreeStepsH.keepRO` is the refine instance). -/
theorem FreeStepsH.keepRO_of {X : Type} {p : ByteArray} {R : HostRel X} {lo hi : Nat} (hR : KeepsRO R lo hi)
    {i i' n : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : X}
    (run : FreeStepsH p R i ω μ x i' ω' μ' x' n) :
    (∀ q, (q < lo ∨ hi ≤ q) → μ'.pages.get? q = μ.pages.get? q) ∧
      ∀ b, b < two32 → (b / pageSize < lo ∨ hi ≤ b / pageSize) → μ.writable b = false →
        μ'.read b = μ.read b := by
  induction run with
  | refl => exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | pad _ ih => exact ih
  | next hn _ _ ih =>
    obtain ⟨P, -, hs⟩ := hn
    obtain ⟨hp, hk⟩ := P.freeStep_keep hs
    refine ⟨fun q hq => by rw [ih.1 q hq, hp], fun b hb hq hw => ?_⟩
    have hw2 : _ := hw
    unfold Memory.writable at hw2
    rw [ih.2 b hb hq (by unfold Memory.writable; rw [hp]; exact hw2), hk b hb hw]
  | host _ _ _ hr _ ih =>
    obtain ⟨hp, hk⟩ := hR _ _ _ _ _ _ _ hr
    refine ⟨fun q hq => by rw [ih.1 q hq, hp q hq], fun b hb hq hw => ?_⟩
    have hw2 : _ := hw
    unfold Memory.writable at hw2
    rw [ih.2 b hb hq (by unfold Memory.writable; rw [hp _ hq]; exact hw2), hk b hb hw]

end JAM
