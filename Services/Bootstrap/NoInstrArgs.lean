import Services.Bootstrap.Prefix
import Services.Bootstrap.BParams
import Services.Bootstrap.Glue

/-!
# Bootstrap's refine on an empty instruction list: the arguments' decodes

From Y's state, for every core index c < 2^16, item index i < 2^16, service id s < 2^32, 32-octet
salt and 32-octet hash, with the payload ℰ(`Instructions { [], salt }`) = [0] ⌢ salt: the prefix,
the parameter chain `BParams`, and the decodes of c, i, s and |y| = 33 with the steps between them
(`Glue`), to 35130, where the payload's Vec is read. The post states what `NoInstrHead` needs.
-/

namespace Services.Bootstrap.NoInstrArgs

macro "tail_facts" : tactic => `(tactic| first | assumption | chase)

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Prefix

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

/-- `HeapPages` depends only on which pages are writable. -/
theorem heapPages_of_writable {μ μ' : Memory} {a b h : Nat} (hw : ∀ x, μ'.writable x = μ.writable x)
    (hp : JAM.HeapPages μ a b h) : JAM.HeapPages μ' a b h := by
  intro q h1 h2
  have := hw (q * pageSize)
  simp only [Memory.writable, Nat.mul_div_cancel _ (show 0 < pageSize by decide)] at this
  rw [this]; exact hp q h1 h2

/-- `prefix_run`, keeping the heap's pages (`PrefixC.run` states them; `PrefixPost` does not). -/
theorem prefix_run_pages (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (L : Nat) (hL : 0 < L ∧ L ≤ 16777216) (hμ : StartMem μ) :
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 38875 ω' μ' x' 600 ∧
      PrefixPost L μ ω' μ' x' ∧ JAM.HeapPages μ' 48 1044430 51 := by
  obtain ⟨ω', μ', hrun, hregs, hmem, hsym, hfr, hrdA, hrdm, hwrm, hpg⟩ :=
    PrefixC.run p P env (initRegs L) μ ((∅, []) : RefineCtx) henv hpar L ⟨hL.1, by omega⟩ (by simp [initRegs]) (by simp [initRegs]) (by simp [initRegs]) (by simp [initRegs]) (by simp [initRegs]) (by simp [initRegs]) (by simp [initRegs]) (by rw [show μ.readN 206512 4 = [μ.read 206512, μ.read 206513, μ.read 206514, μ.read 206515] from rfl, hμ.bytes 206512 0 (by decide), hμ.bytes 206513 0 (by decide), hμ.bytes 206514 0 (by decide), hμ.bytes 206515 0 (by decide)]) (by rw [show μ.readN 206520 8 = [μ.read 206520, μ.read 206521, μ.read 206522, μ.read 206523, μ.read 206524, μ.read 206525, μ.read 206526, μ.read 206527] from rfl, hμ.bytes 206520 0 (by decide), hμ.bytes 206521 0 (by decide), hμ.bytes 206522 0 (by decide), hμ.bytes 206523 0 (by decide), hμ.bytes 206524 0 (by decide), hμ.bytes 206525 0 (by decide), hμ.bytes 206526 0 (by decide), hμ.bytes 206527 0 (by decide)]) (by rw [show μ.readN 206824 8 = [μ.read 206824, μ.read 206825, μ.read 206826, μ.read 206827, μ.read 206828, μ.read 206829, μ.read 206830, μ.read 206831] from rfl, hμ.bytes 206824 0 (by decide), hμ.bytes 206825 0 (by decide), hμ.bytes 206826 0 (by decide), hμ.bytes 206827 0 (by decide), hμ.bytes 206828 0 (by decide), hμ.bytes 206829 0 (by decide), hμ.bytes 206830 0 (by decide), hμ.bytes 206831 0 (by decide)]) (by rw [show μ.readN 206832 8 = [μ.read 206832, μ.read 206833, μ.read 206834, μ.read 206835, μ.read 206836, μ.read 206837, μ.read 206838, μ.read 206839] from rfl, hμ.bytes 206832 0 (by decide), hμ.bytes 206833 0 (by decide), hμ.bytes 206834 0 (by decide), hμ.bytes 206835 0 (by decide), hμ.bytes 206836 0 (by decide), hμ.bytes 206837 0 (by decide), hμ.bytes 206838 0 (by decide), hμ.bytes 206839 0 (by decide)]) (by rw [show μ.readN 206848 4 = [μ.read 206848, μ.read 206849, μ.read 206850, μ.read 206851] from rfl, hμ.bytes 206848 0 (by decide), hμ.bytes 206849 0 (by decide), hμ.bytes 206850 0 (by decide), hμ.bytes 206851 0 (by decide)]) (by rw [show μ.readN 4278058160 8 = [μ.read 4278058160, μ.read 4278058161, μ.read 4278058162, μ.read 4278058163, μ.read 4278058164, μ.read 4278058165, μ.read 4278058166, μ.read 4278058167] from rfl, hμ.bytes 4278058160 0 (by decide), hμ.bytes 4278058161 0 (by decide), hμ.bytes 4278058162 0 (by decide), hμ.bytes 4278058163 0 (by decide), hμ.bytes 4278058164 0 (by decide), hμ.bytes 4278058165 0 (by decide), hμ.bytes 4278058166 0 (by decide), hμ.bytes 4278058167 0 (by decide)]) (by rw [show μ.readN 4278058168 8 = [μ.read 4278058168, μ.read 4278058169, μ.read 4278058170, μ.read 4278058171, μ.read 4278058172, μ.read 4278058173, μ.read 4278058174, μ.read 4278058175] from rfl, hμ.bytes 4278058168 0 (by decide), hμ.bytes 4278058169 0 (by decide), hμ.bytes 4278058170 0 (by decide), hμ.bytes 4278058171 0 (by decide), hμ.bytes 4278058172 0 (by decide), hμ.bytes 4278058173 0 (by decide), hμ.bytes 4278058174 0 (by decide), hμ.bytes 4278058175 0 (by decide)]) (fun a h1 h2 => by first | exact hμ.stack a (by omega) (by omega) | exact hμ.heap a (by omega) (by omega)) (fun a h1 h2 => by first | exact hμ.stack a (by omega) (by omega) | exact hμ.heap a (by omega) (by omega)) (fun a h1 h2 => by first | exact hμ.stack a (by omega) (by omega) | exact hμ.heap a (by omega) (by omega)) (fun a h1 h2 => by first | exact hμ.stack a (by omega) (by omega) | exact hμ.heap a (by omega) (by omega)) (fun a h1 h2 => by first | exact hμ.stack a (by omega) (by omega) | exact hμ.heap a (by omega) (by omega)) (fun a h1 h2 => by first | exact hμ.stack a (by omega) (by omega) | exact hμ.heap a (by omega) (by omega)) (fun a h1 h2 => by first | exact hμ.stack a (by omega) (by omega) | exact hμ.heap a (by omega) (by omega)) (fun a h1 h2 => by first | exact hμ.stack a (by omega) (by omega) | exact hμ.heap a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) (fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega)) hμ.heapPages
  refine ⟨ω', μ', _, hrun, ⟨?regs, ?bytes, ?args, ?argsRd, ?stk, ?hp, rfl, ?lw, ?ro, ?fr⟩, hpg⟩
  case regs =>
    clear hfr hrdA hrdm hwrm hmem hsym hrun
    simp [initRegs] at hregs
    simp [hregs]
  case bytes =>
    simp only [postBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    simp [hmem]
  case args =>
    intro a h1 h2
    apply hfr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
      Nat.not_lt]
    omega
  case argsRd => intro a h1 h2; exact hrdA a (by omega)
  case stk => intro a h1 h2; exact hwrm a (hμ.stack a h1 h2)
  case hp => intro a h1 h2; exact hwrm a (hμ.heap a h1 h2)
  case lw =>
    simp only [lenAt, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact hsym
  case ro => intro a h1 h2; exact hrdm a (hμ.ro a h1 h2)
  case fr =>
    first
    | exact hfr
    | (intro a ha
       apply hfr
       simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
         Nat.not_lt] at ha ⊢
       omega)

theorem run_args (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (hμ : StartMem μ) (C I S : Nat) (h : List UInt8) (hC : C < 65536) (hI : I < 65536)
    (hS : S < 4294967296) (salt : List UInt8) (hsalt : salt.length = 32) (hh : h.length = 32) (L : Nat)
    (hLdef : (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1 + 33 + 32 = L)
    (hmem : μ.readN 4278124544 L = Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat 33 ++ (0 :: salt) ++ h)
    (hrd : ∀ j, 4278124544 ≤ j → j < 4278124544 + L → μ.readable j = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 35130 ω' μ'
      ((∅, []) : RefineCtx) 6000 ∧
      (ω'[1] = UInt64.ofNat 4278058264) ∧
      (ω'[4] = UInt64.ofNat 8) ∧
      (ω'[5] = UInt64.ofNat 4278058544) ∧
      (ω'[6] = UInt64.ofNat 4278124544) ∧
      (ω'[7] = UInt64.ofNat 0) ∧
      (ω'[8] = UInt64.ofNat 33) ∧
      (μ'.readN 206512 8 = [0, 0, 0, 0, 32, 40, 3, 0]) ∧
      (μ'.readN 206520 8 = [32, 40, 3, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 206824 8 = [0, 0, 0, 0, 0, 0, 0, 128]) ∧
      (μ'.readN 206832 8 = [0, 0, 0, 0, 32, 0, 0, 0]) ∧
      (μ'.readN 206840 4 = [6, 0, 0, 0]) ∧
      (μ'.readN 206848 4 = [0, 0, 0, 0]) ∧
      (μ'.readN 206880 8 = [0, 0, 0, 0, 0, 0, 0, 4]) ∧
      (μ'.readN 206888 4 = [0, 0, 0, 0]) ∧
      (μ'.readN 4278058312 8 = [65, 0, 0, 0, 0, 0, 0, 0]) ∧
      (∀ a, 196608 ≤ a → a < 196616 → μ'.writable a = true) ∧
      (∀ a, 206512 ≤ a → a < 206520 → μ'.writable a = true) ∧
      (∀ a, 206824 ≤ a → a < 206840 → μ'.writable a = true) ∧
      (∀ a, 206848 ≤ a → a < 206852 → μ'.writable a = true) ∧
      (∀ a, 206880 ≤ a → a < 206888 → μ'.writable a = true) ∧
      (∀ a, 206976 ≤ a → a < 206992 → μ'.writable a = true) ∧
      (∀ a, 4278057992 ≤ a → a < 4278058264 → μ'.writable a = true) ∧
      (∀ a, 206512 ≤ a → a < 206528 → μ'.readable a = true) ∧
      (∀ a, 206824 ≤ a → a < 206844 → μ'.readable a = true) ∧
      (∀ a, 206848 ≤ a → a < 206852 → μ'.readable a = true) ∧
      (∀ a, 206880 ≤ a → a < 206892 → μ'.readable a = true) ∧
      (∀ a, 4278057992 ≤ a → a < 4278058016 → μ'.readable a = true) ∧
      (∀ a, 4278058024 ≤ a → a < 4278058128 → μ'.readable a = true) ∧
      (∀ a, 4278058136 ≤ a → a < 4278058176 → μ'.readable a = true) ∧
      (∀ a, 4278058184 ≤ a → a < 4278058200 → μ'.readable a = true) ∧
      (∀ a, 4278058224 ≤ a → a < 4278058232 → μ'.readable a = true) ∧
      (∀ a, 4278058312 ≤ a → a < 4278058320 → μ'.readable a = true) ∧
      (μ'.readN 66657 7 = [26, 66, 111, 111, 116, 115, 116]) ∧
      (μ'.readN 66664 8 = [114, 97, 112, 32, 83, 101, 114, 118]) ∧
      (μ'.readN 66672 8 = [105, 99, 101, 32, 82, 101, 102, 105]) ∧
      (μ'.readN 66680 8 = [110, 101, 44, 32, 192, 1, 104, 0]) ∧
      (μ'.readN 71060 4 = [48, 49, 50, 51]) ∧
      (μ'.readN 71064 8 = [52, 53, 54, 55, 56, 57, 97, 98]) ∧
      (μ'.readN 71072 4 = [99, 100, 101, 102]) ∧
      (μ'.readN 77040 8 = [36, 10, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058352 8 = [0, 0, 255, 254, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058368 8 = [152, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058360 8 = Num.encodeLE 8 L) ∧
      (∀ a, 206512 ≤ a → a < 206516 → μ'.writable a = true) ∧
      (∀ a, 206824 ≤ a → a < 206844 → μ'.writable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207036 → μ'.writable a = true) ∧
      (∀ a, 207072 ≤ a → a < 207088 → μ'.writable a = true) ∧
      (∀ a, 4278057712 ≤ a → a < 4278057720 → μ'.writable a = true) ∧
      (∀ a, 4278057728 ≤ a → a < 4278057752 → μ'.writable a = true) ∧
      (∀ a, 4278057984 ≤ a → a < 4278058000 → μ'.writable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058088 → μ'.writable a = true) ∧
      (∀ a, 4278058104 ≤ a → a < 4278058376 → μ'.writable a = true) ∧
      (∀ a, 4278058456 ≤ a → a < 4278058472 → μ'.writable a = true) ∧
      (∀ a, 4278058488 ≤ a → a < 4278058496 → μ'.writable a = true) ∧
      (∀ a, 4278058544 ≤ a → a < 4278058610 → μ'.writable a = true) ∧
      (∀ a, 4278058620 ≤ a → a < 4278058624 → μ'.writable a = true) ∧
      (∀ a, 4278058648 ≤ a → a < 4278058664 → μ'.writable a = true) ∧
      (∀ a, 66657 ≤ a → a < 66688 → μ'.readable a = true) ∧
      (∀ a, 71060 ≤ a → a < 71076 → μ'.readable a = true) ∧
      (∀ a, 77040 ≤ a → a < 77048 → μ'.readable a = true) ∧
      (∀ a, 206512 ≤ a → a < 206516 → μ'.readable a = true) ∧
      (∀ a, 206520 ≤ a → a < 206528 → μ'.readable a = true) ∧
      (∀ a, 206884 ≤ a → a < 206888 → μ'.readable a = true) ∧
      (∀ a, 206912 ≤ a → a < 206913 → μ'.readable a = true) ∧
      (∀ a, 206976 ≤ a → a < 206988 → μ'.readable a = true) ∧
      (∀ a, 207076 ≤ a → a < 207084 → μ'.readable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058072 → μ'.readable a = true) ∧
      (∀ a, 4278058104 ≤ a → a < 4278058120 → μ'.readable a = true) ∧
      (∀ a, 4278058128 ≤ a → a < 4278058376 → μ'.readable a = true) ∧
      (∀ a, 4278058488 ≤ a → a < 4278058496 → μ'.readable a = true) ∧
      (∀ a, 4278058544 ≤ a → a < 4278058568 → μ'.readable a = true) ∧
      (∀ a, 4278058600 ≤ a → a < 4278058604 → μ'.readable a = true) ∧
      (∀ a, 4278058620 ≤ a → a < 4278058624 → μ'.readable a = true) ∧
      (∀ a, 4278058648 ≤ a → a < 4278058664 → μ'.readable a = true) ∧
      (JAM.HeapPages μ' 48 1044430 51) ∧
      (∀ a, 207008 ≤ a → a < 207037 → μ'.writable a = true) ∧
      (∀ a, 4278057744 ≤ a → a < 4278057752 → μ'.readable a = true) ∧
      (∀ a, 4278058072 ≤ a → a < 4278058088 → μ'.readable a = true) ∧
      (∀ a, 4278058104 ≤ a → a < 4278058376 → μ'.readable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207038 → μ'.writable a = true) ∧
      (∀ a, 4278057736 ≤ a → a < 4278057752 → μ'.readable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058088 → μ'.readable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207039 → μ'.writable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207040 → μ'.writable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207041 → μ'.writable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207042 → μ'.writable a = true) ∧
      (∀ a, 4278057736 ≤ a → a < 4278057744 → μ'.readable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207043 → μ'.writable a = true) ∧
      (∀ a, 196608 ≤ a → a < 196616 → μ'.readable a = true) ∧
      (μ'.readN 4278058280 8 = Num.encodeLE 8 S) ∧
      (μ'.readN 4278058288 8 = Num.encodeLE 8 I) ∧
      (μ'.readN 4278058296 8 = Num.encodeLE 8 C) ∧
      (μ'.readN 4278058304 8 = Num.encodeLE 8 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1)) ∧
      (μ'.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1) 33 = 0 :: salt) ∧
      (∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ'.readable a = true) ∧
      (∀ a, 4278057688 ≤ a → a < 4278059008 → μ'.writable a = true) ∧
      (∀ a, 196608 ≤ a → a < 208896 → μ'.writable a = true) ∧
      (μ'.readN 66099 5 = [10, 82, 101, 116, 117]) ∧
      (μ'.readN 66104 8 = [114, 110, 105, 110, 103, 32, 192, 16]) ∧
      (μ'.readN 66112 8 = [32, 105, 110, 116, 111, 32, 97, 99]) ∧
      (μ'.readN 66120 8 = [99, 117, 109, 117, 108, 97, 116, 101]) ∧
      (μ'.readN 66128 1 = [0]) ∧
      (μ'.readN 72826 1 = [93]) ∧
      (μ'.readN 72829 1 = [91]) ∧
      (μ'.readN 196800 4 = [0, 0, 0, 0]) ∧
      (μ'.readN 206528 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058984 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058992 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278059000 8 = [0, 0, 255, 255, 0, 0, 0, 0]) ∧
      (∀ a, 196800 ≤ a → a < 196804 → μ'.writable a = true) ∧
      (∀ a, 206528 ≤ a → a < 206536 → μ'.writable a = true) ∧
      (∀ a, 206880 ≤ a → a < 206896 → μ'.writable a = true) ∧
      (∀ a, 207040 ≤ a → a < 207056 → μ'.writable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058376 → μ'.writable a = true) ∧
      (∀ a, 4278058496 ≤ a → a < 4278058504 → μ'.writable a = true) ∧
      (∀ a, 4278058544 ≤ a → a < 4278058600 → μ'.writable a = true) ∧
      (∀ a, 4278058624 ≤ a → a < 4278058680 → μ'.writable a = true) ∧
      (∀ a, 66099 ≤ a → a < 66129 → μ'.readable a = true) ∧
      (∀ a, 72826 ≤ a → a < 72827 → μ'.readable a = true) ∧
      (∀ a, 72829 ≤ a → a < 72830 → μ'.readable a = true) ∧
      (∀ a, 196800 ≤ a → a < 196804 → μ'.readable a = true) ∧
      (∀ a, 206520 ≤ a → a < 206536 → μ'.readable a = true) ∧
      (∀ a, 206880 ≤ a → a < 206888 → μ'.readable a = true) ∧
      (∀ a, 207008 ≤ a → a < 207011 → μ'.readable a = true) ∧
      (∀ a, 4278058064 ≤ a → a < 4278058376 → μ'.readable a = true) ∧
      (∀ a, 4278058456 ≤ a → a < 4278058472 → μ'.readable a = true) ∧
      (∀ a, 4278058544 ≤ a → a < 4278058570 → μ'.readable a = true) ∧
      (∀ a, 4278058624 ≤ a → a < 4278058680 → μ'.readable a = true) ∧
      (∀ a, 4278058984 ≤ a → a < 4278059008 → μ'.readable a = true) := by
  have hwC := encodeNat_len_le3 C hC
  have hwI := encodeNat_len_le3 I hI
  have hwS := encodeNat_len_le5 S hS
  have hw33 : (Blob.encodeNat 33).length = 1 := by decide
  obtain ⟨ω1, μ1, x1, run1, post1, hpg1⟩ := prefix_run_pages p P env henv hpar μ L ⟨by omega, by omega⟩ hμ
  obtain ⟨r1_0, r1_1, r1_2, r1_3, r1_4, r1_5, r1_6, r1_7, r1_8, r1_9, r1_12⟩ := post1.regs
  have hx1 := post1.ctx
  subst hx1
  have hst1 := post1.stack
  have hhp1 := post1.heap
  have hfr1 := post1.frame
  have hag1 := post1.args
  have har1 := post1.argsRd
  have hro1 := post1.ro
  have hlw1 := post1.lenWords
  simp only [lenAt, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true] at hlw1
  have pb1 := post1.bytes
  simp only [postBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at pb1
  have ib0 : ∀ q ∈ baseBytes, μ.read q.1 = q.2 := fun q hq => hμ.bytes q.1 q.2 hq
  simp only [baseBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at ib0
  have ip0 : ∀ q ∈ pathBytes, μ.read q.1 = q.2 := fun q hq => hμ.path q.1 q.2 hq
  simp only [pathBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at ip0
  -- the parameter chain, to the core index's decode at 4642
  refine (fun h2 => ?_) (BParams.run p P env ω1 μ1 ((∅, []) : RefineCtx) L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · obtain ⟨ω2, μ2, run2, g2, m2, s2, f2, rd2, wr2⟩ := h2
    obtain ⟨g2_0, g2_1, g2_2, g2_3, g2_4, g2_5, g2_6, g2_7, g2_8, g2_10, g2_11, g2_12, g2_9⟩ := g2
    obtain ⟨s2a, s2b⟩ := s2
    -- the arguments, sliced
    have sC : μ.readN 4278124544 (Blob.encodeNat C).length = Blob.encodeNat C := by
      have := Memory.readN_mid μ 4278124544 [] (Blob.encodeNat C)
        (Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 33 ++ (0 :: salt) ++ h)
        (by
          rw [show (([] : List UInt8) ++ Blob.encodeNat C ++ (Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 33 ++ (0 :: salt) ++ h)).length = L by
            simp [hh, hw33, hsalt]; omega]
          simpa only [List.nil_append, List.append_assoc] using hmem)
      simpa using this
    -- the arguments are as they started, up to the core index's decode
    have arg2 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ2.read a = μ.read a := fun a h1 h2 =>
      (f2 a (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans
        (hag1 a h1 h2)
    -- 4642: the return address of the inlined decode
    obtain ⟨ω3, run3, e3_0, e3fr⟩ : ∃ ω3, FreeStepsH p (refineContract env) 4642 ω2 μ2 ((∅, []) : RefineCtx) 4646 ω3 μ2
        ((∅, []) : RefineCtx) 1 ∧ ω3[0] = UInt64.ofNat 1634 ∧ ∀ j : Fin 13, j.val ≠ 0 → ω3[j] = ω2[j] := by
      rw [show ω2 = regsNF ω2 [] from rfl]
      refine ⟨?ω₃, ?r, ?e0, fun j hj => ?fr⟩
      case r => pvm_go []
      case e0 => simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
      case fr =>
        simp only [Fin.getElem_fin]
        rw [PVM.getElem_regsNF _ _ _ j.isLt]
        simp [PVM.lookup_cons_nat, hj]
        rfl
    -- c
    obtain ⟨ω4, μ4, run4, d4_0, d4_1, d4_2, d4_3, d4_4, d4_5, d4_6, d4_12, d4_7, d4_8, d4_r0, d4_r8, d4_fr, d4_rd, d4_wr⟩ :=
      decodeU16 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω3 μ2 1634 35073 4278058264
        4278058304 4278124544 L e3_0 ((e3fr 1 (by decide)).trans g2_1) ((e3fr 7 (by decide)).trans g2_7) (by decide)
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_816]) bs_35073 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (fun a h1 h2 => by rw [wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr2]; exact hst1 a (by omega) (by omega))
        (by chase) (by chase) C hC ⟨by omega, by omega⟩
        (fun a h1 h2 => by rw [rd2, har1 a h1 (by omega)]; exact hrd a h1 (by omega))
        (by rw [Memory.readN_congr (fun j hj => arg2 _ (by omega) (by omega))]; exact sC)
    have arg4 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ4.read a = μ.read a := fun a h1 h2 =>
      (d4_fr a (by omega) (by omega) (by omega)).trans (arg2 a h1 h2)
    -- store c, call the decode of i
    obtain ⟨ω5, run5, e5_0, e5_1, e5_7, e5fr⟩ := glueC (p := p) (P := P) (R := refineContract env)
      ((∅, []) : RefineCtx) ω4 μ4 C (by omega) d4_7 d4_8 (d4_1.trans ((e3fr 1 (by decide)).trans g2_1))
      (fun a h1 h2 => by rw [d4_wr, wr2]; exact hst1 a (by omega) (by omega))
    have arg5 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L →
        (μ4.writeN 4278058296 (Num.encodeLE 8 C)).read a = μ.read a := fun a h1 h2 => by
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)]
      exact arg4 a h1 h2
    have sI : μ.readN (4278124544 + (Blob.encodeNat C).length) (Blob.encodeNat I).length = Blob.encodeNat I := by
      apply Memory.readN_mid μ 4278124544 (Blob.encodeNat C) (Blob.encodeNat I)
        (Blob.encodeNat S ++ Blob.encodeNat 33 ++ (0 :: salt) ++ h)
      rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ (Blob.encodeNat S ++ Blob.encodeNat 33 ++ (0 :: salt) ++ h)).length = L by
        simp [hh, hw33, hsalt]; omega]
      simpa only [List.append_assoc] using hmem
    -- i
    obtain ⟨ω6, μ6, run6, d6_0, d6_1, d6_2, d6_3, d6_4, d6_5, d6_6, d6_12, d6_7, d6_8, d6_r0, d6_r8, d6_fr, d6_rd, d6_wr⟩ :=
      decodeU32 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω5 (μ4.writeN 4278058296 (Num.encodeLE 8 C)) 1636 35092 4278058264
        4278058304 (4278124544 + (Blob.encodeNat C).length) (L - (Blob.encodeNat C).length) e5_0 e5_1 e5_7
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_817]) bs_35092 (by decide) (by decide)
        (by omega) (by omega) (by omega) (by omega)
        (fun a h1 h2 => by rw [Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (by
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32])]
          exact d4_r0)
        (by
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32])]
          exact d4_r8)
        I (by omega) ⟨by omega, by omega⟩
        (fun a h1 h2 => by
          rw [Memory.readable_writeN, d4_rd, rd2, har1 a (by omega) (by omega)]; exact hrd a (by omega) (by omega))
        (by rw [Memory.readN_congr (fun j hj => arg5 _ (by omega) (by omega))]; exact sI)
    have arg6 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ6.read a = μ.read a := fun a h1 h2 =>
      (d6_fr a (by omega) (by omega) (by omega)).trans (arg5 a h1 h2)
    -- store i, call the decode of s
    obtain ⟨ω7, run7, e7_0, e7_1, e7_7, e7fr⟩ := glueI (p := p) (P := P) (R := refineContract env)
      ((∅, []) : RefineCtx) ω6 μ6 I (by omega) d6_7 d6_8 (d6_1.trans e5_1)
      (fun a h1 h2 => by rw [d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
    have arg7 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L →
        (μ6.writeN 4278058288 (Num.encodeLE 8 I)).read a = μ.read a := fun a h1 h2 => by
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)]
      exact arg6 a h1 h2
    have sS : μ.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length) (Blob.encodeNat S).length =
        Blob.encodeNat S := by
      have := Memory.readN_mid μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I) (Blob.encodeNat S)
        (Blob.encodeNat 33 ++ (0 :: salt) ++ h)
        (by
          rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ (Blob.encodeNat 33 ++ (0 :: salt) ++ h)).length = L by
            simp [hh, hw33, hsalt]; omega]
          simpa only [List.append_assoc] using hmem)
      simpa [Nat.add_assoc] using this
    obtain ⟨ω8, μ8, run8, d8_0, d8_1, d8_2, d8_3, d8_4, d8_5, d8_6, d8_12, d8_7, d8_8, d8_r0, d8_r8, d8_fr, d8_rd, d8_wr⟩ :=
      decodeU32 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω7 (μ6.writeN 4278058288 (Num.encodeLE 8 I))
        1638 35111 4278058264 4278058304 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length)
        (L - (Blob.encodeNat C).length - (Blob.encodeNat I).length) e7_0 e7_1 e7_7
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_818]) bs_35111 (by decide) (by decide)
        (by omega) (by omega) (by omega) (by omega)
        (fun a h1 h2 => by rw [Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (by
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d6_r0])
        (by
          rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d6_r8, Nat.sub_sub])
        S hS ⟨by omega, by omega⟩
        (fun a h1 h2 => by
          rw [Memory.readable_writeN, d6_rd, Memory.readable_writeN, d4_rd, rd2, har1 a (by omega) (by omega)]
          exact hrd a (by omega) (by omega))
        (by rw [Memory.readN_congr (fun j hj => arg7 _ (by omega) (by omega))]; exact sS)
    have arg8 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ8.read a = μ.read a := fun a h1 h2 =>
      (d8_fr a (by omega) (by omega) (by omega)).trans (arg7 a h1 h2)
    -- store s, call the decode of |y|
    obtain ⟨ω9, run9, e9_0, e9_1, e9_7, e9fr⟩ := glueS (p := p) (P := P) (R := refineContract env)
      ((∅, []) : RefineCtx) ω8 μ8 S (by omega) d8_7 d8_8 (d8_1.trans e7_1)
      (fun a h1 h2 => by rw [d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
    have arg9 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L →
        (μ8.writeN 4278058280 (Num.encodeLE 8 S)).read a = μ.read a := fun a h1 h2 => by
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)]
      exact arg8 a h1 h2
    have sY : μ.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length)
        (Blob.encodeNat 33).length = Blob.encodeNat 33 := by
      have := Memory.readN_mid μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S) (Blob.encodeNat 33)
        ((0 :: salt) ++ h)
        (by
          rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 33 ++ ((0 :: salt) ++ h)).length = L by
            simp [hh, hw33, hsalt]; omega]
          simpa only [List.append_assoc] using hmem)
      simpa [Nat.add_assoc] using this
    obtain ⟨ω10, μ10, run10, d10_0, d10_1, d10_2, d10_3, d10_4, d10_5, d10_6, d10_12, d10_7, d10_8, d10_r0, d10_r8, d10_fr, d10_rd, d10_wr⟩ :=
      decodeU32 (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω9 (μ8.writeN 4278058280 (Num.encodeLE 8 S))
        1640 35130 4278058264 4278058304
        (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length)
        (L - (Blob.encodeNat C).length - (Blob.encodeNat I).length - (Blob.encodeNat S).length) e9_0 e9_1 e9_7
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_819]) bs_35130 (by decide) (by decide)
        (by omega) (by omega) (by omega) (by omega)
        (fun a h1 h2 => by rw [Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]; exact hst1 a (by omega) (by omega))
        (by rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d8_r0])
        (by rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]), d8_r8, Nat.sub_sub])
        33 (by omega) ⟨by omega, by omega⟩
        (fun a h1 h2 => by
          rw [Memory.readable_writeN, d8_rd, Memory.readable_writeN, d6_rd, Memory.readable_writeN, d4_rd, rd2,
            har1 a (by omega) (by omega)]
          exact hrd a (by omega) (by omega))
        (by rw [Memory.readN_congr (fun j hj => arg9 _ (by omega) (by omega))]; exact sY)
    have arg10 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ10.read a = μ.read a := fun a h1 h2 =>
      (d10_fr a (by omega) (by omega) (by omega)).trans (arg9 a h1 h2)
    have q10_4 : ω10[4] = UInt64.ofNat 8 := d10_4.trans ((e9fr 4 (by decide)).trans (d8_4.trans ((e7fr 4 (by decide)).trans (d6_4.trans ((e5fr 4 (by decide)).trans (d4_4.trans ((e3fr 4 (by decide)).trans g2_4)))))))
    have q10_5 : ω10[5] = UInt64.ofNat 4278058544 := d10_5.trans ((e9fr 5 (by decide)).trans (d8_5.trans ((e7fr 5 (by decide)).trans (d6_5.trans ((e5fr 5 (by decide)).trans (d4_5.trans ((e3fr 5 (by decide)).trans g2_5)))))))
    have q10_6 : ω10[6] = UInt64.ofNat 4278124544 := d10_6.trans ((e9fr 6 (by decide)).trans (d8_6.trans ((e7fr 6 (by decide)).trans (d6_6.trans ((e5fr 6 (by decide)).trans (d4_6.trans ((e3fr 6 (by decide)).trans g2_6)))))))
    have q10_r8 : μ10.readN 4278058312 8 = [65, 0, 0, 0, 0, 0, 0, 0] := by
      have := d10_r8
      rw [hw33, show L - (Blob.encodeNat C).length - (Blob.encodeNat I).length - (Blob.encodeNat S).length - 1 = 65 by
        omega] at this
      simpa [Num.encodeLE] using this
    -- the stored c, i, s and L, at μ10
    have p10S : μ10.readN 4278058280 8 = Num.encodeLE 8 S := by
      rw [Memory.readN_congr (fun j hj => d10_fr _ (by omega) (by omega) (by omega))]
      exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    have p10I : μ10.readN 4278058288 8 = Num.encodeLE 8 I := by
      rw [Memory.readN_congr (fun j hj => (d10_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        (d8_fr _ (by omega) (by omega) (by omega))))]
      exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    have p10C : μ10.readN 4278058296 8 = Num.encodeLE 8 C := by
      rw [Memory.readN_congr (fun j hj => (d10_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        ((d8_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        (d6_fr _ (by omega) (by omega) (by omega))))))]
      exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    have p10L : μ10.readN 4278058360 8 = Num.encodeLE 8 L := by
      rw [Memory.readN_congr (fun j hj => (d10_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        ((d8_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        ((d6_fr _ (by omega) (by omega) (by omega)).trans
        ((Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]) (by simp [two32] <;> omega)).trans
        (d4_fr _ (by omega) (by omega) (by omega))))))))]
      exact s2b
    -- the payload, sliced
    have sP : μ.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1)
        (0 :: salt).length = 0 :: salt := by
      have := Memory.readN_mid μ 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 33)
        (0 :: salt) h
        (by
          rw [show (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 33 ++ (0 :: salt) ++ h).length = L by
            simp [hh, hw33, hsalt]; omega]
          exact hmem)
      simpa [hw33, Nat.add_assoc] using this
    have hrd10 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ10.readable a = true := fun a h1 h2 => by
      rw [d10_rd, Memory.readable_writeN, d8_rd, Memory.readable_writeN, d6_rd, Memory.readable_writeN, d4_rd,
        rd2, har1 a h1 h2]
      exact hrd a h1 h2
    have hwr10 : ∀ a, 4278057688 ≤ a → a < 4278059008 → μ10.writable a = true := fun a h1 h2 => by
      rw [d10_wr, Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]
      exact hst1 a (by omega) (by omega)
    have hwh10 : ∀ a, 196608 ≤ a → a < 208896 → μ10.writable a = true := fun a h1 h2 => by
      rw [d10_wr, Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]
      exact hhp1 a h1 h2
    have sP10 : μ10.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length +
        (Blob.encodeNat S).length + 1) 33 = 0 :: salt := by
      rw [Memory.readN_congr (fun j hj => arg10 _ (by omega) (by omega)), show (33 : Nat) = (0 :: salt).length by
        simp [hsalt]]
      exact sP
    have r10 : μ10.readN 4278058304 8 = Num.encodeLE 8 (4278124544 + (Blob.encodeNat C).length +
        (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1) := by
      rw [d10_r0, hw33]
    have hpg10 : JAM.HeapPages μ10 48 1044430 51 := heapPages_of_writable (fun x => by
      rw [d10_wr, Memory.writable_writeN, d8_wr, Memory.writable_writeN, d6_wr, Memory.writable_writeN, d4_wr, wr2]) hpg1
    refine ⟨ω10, μ10, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
      (run8.trans (run9.trans run10))))))))).mono (by omega), ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals tail_facts
  all_goals first
    | chase
    | (intro a h1 h2; first
        | exact Memory.readable_of_writable (hhp1 a (by omega) (by omega))
        | exact Memory.readable_of_writable (hst1 a (by omega) (by omega)))

end Services.Bootstrap.NoInstrArgs
