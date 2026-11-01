import PVM.Invocation
import PVM.Theorems.Host
import PVM.Theorems.Termination

/-!
# A program's host calls are bounded by its `ecalli` immediates

`hostCallIdsOf p` scans a blob for `ecalli` instructions without running it. We prove:

* `psi_hostId_mem`: every h̵ × h that Ψ returns has h among them;
* `psiHStar_congr`, `psiM_congr`: running a program under two host handlers that agree on those
  ids gives the same result. A program's behaviour cannot depend on what a handler does for any
  other id, so in particular it can never make any other host call.
-/

namespace PVM

theorem deblob_vInst {p : ByteArray} {i : Nat} {P : Program} (h : deblob p i = some P) :
    P.vInst i = true := by
  unfold deblob at h
  cases hp : Blob.parse? p with
  | none => simp [hp] at h
  | some P' =>
    simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h; rename_i hv; simp only [Bool.and_eq_true] at hv; exact hv.2
    · cases h

/-- **Every host call Ψ makes is one the program names.** -/
theorem psi_hostId_mem {p : ByteArray} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs}
    {μ : Memory} {h : UInt64} (hs : (psi p i gas ch ω μ).status = .host h) :
    h.toNat ∈ hostCallIdsOf p := by
  obtain ⟨P, hP, hdec⟩ := psi_host hs
  obtain ⟨hparse, hlt⟩ := deblob_some hP
  have hv := deblob_vInst hP
  simp only [hostCallIdsOf, hparse, Program.hostCallIds, List.mem_filterMap, List.mem_range]
  exact ⟨_, hlt, by simp [hv, hdec]⟩

variable {X : Type}

/-- Two handlers agree on the ids in `S`. -/
def HostFn.AgreeOn (S : List Nat) (f f' : HostFn X) : Prop :=
  ∀ h ∈ S, ∀ g ω μ x, f h g ω μ x = f' h g ω μ x

theorem psiHFuel_congr (p : ByteArray) {f f' : HostFn X}
    (hff : HostFn.AgreeOn (hostCallIdsOf p) f f') :
    ∀ n i gas ch ω μ x, psiHFuel p f n i gas ch ω μ x = psiHFuel p f' n i gas ch ω μ x := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro i gas ch ω μ x
    simp only [psiHFuel]
    generalize hr : psi p i gas ch ω μ = r
    cases hst : r.status
    case host h =>
      have hmem := psi_hostId_mem (hr ▸ hst : (psi p i gas ch ω μ).status = .host h)
      simp only [hff _ hmem r.gas r.regs r.mem x, ih]
    all_goals rfl

/-- **Ψ_H depends only on the handler's behaviour for the program's own `ecalli` ids.** -/
theorem psiHStar_congr (p : ByteArray) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs)
    (μ : Memory) (x : X) {f f' : HostFn X} (hff : HostFn.AgreeOn (hostCallIdsOf p) f f') :
    psiHStar p i gas ch ω μ f x = psiHStar p i gas ch ω μ f' x := by
  simp only [psiHStar, psiHFuel_congr p hff]

/-- The host-call ids of the PVM blob inside a standard JAM blob (GP §A.7). -/
def jamHostCallIdsOf (b : ByteArray) : List Nat :=
  match JamBlob.parse? b with
  | some jb => hostCallIdsOf jb.code
  | none => []

/-- Y returns the PVM blob of the JAM blob it decodes. -/
theorem standardInit_code {b a : ByteArray} {r : ByteArray × Regs × Memory}
    (hY : standardInit b a = some r) : ∃ jb, JamBlob.parse? b = some jb ∧ r.1 = jb.code := by
  unfold standardInit at hY
  obtain ⟨jb, hv, rfl⟩ := Option.map_eq_some_iff.1 hY
  refine ⟨jb, ?_, rfl⟩
  unfold validJamBlob? at hv
  split at hv
  · cases hv
  · obtain ⟨jb', hj, hv'⟩ := Option.bind_eq_some_iff.1 hv
    split at hv'
    · cases hv'
    · cases hv'; exact hj

/-- **Ψ_M depends only on the handler's behaviour for the program's own `ecalli` ids**: a service
    cannot observe, or be affected by, any host function it does not name. -/
theorem psiM_congr (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (x : X)
    {f f' : HostFn X} (hff : HostFn.AgreeOn (jamHostCallIdsOf b) f f') :
    psiM b i gas a f x = psiM b i gas a f' x := by
  unfold psiM
  split
  · rfl
  · rename_i p ω μ hY
    obtain ⟨jb, hj, hp⟩ := standardInit_code hY
    have hff' : HostFn.AgreeOn (hostCallIdsOf p) f f' := by
      simpa [jamHostCallIdsOf, hj, ← hp] using hff
    simp only [psiH, psiHStar_congr p i gas false ω μ x hff']

end PVM
