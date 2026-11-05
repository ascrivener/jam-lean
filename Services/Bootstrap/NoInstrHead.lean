import Services.Bootstrap.ReaderBig
import Services.Bootstrap.GlueY
import Services.Bootstrap.GlueY2
import PVM.Logic.Words
import Services.Bootstrap.NoInstrArgs

/-!
# Bootstrap's refine on an empty instruction list: the payload and the hash

From 35130, where the decodes of c, i, s and |y| = 33 leave the state `NoInstrArgs.run_args`
states: the payload's Vec (`GlueY`), its 33 octets copied to the heap (`read_big`), the steps to the
hash's read (`GlueY2`) and the hash's read (`read_big`), to 35202, where the log of s begins. The
post states what every tail (`VTail1` … `VTail8`) needs.
-/

namespace Services.Bootstrap.NoInstrHead

macro "tail_facts" : tactic => `(tactic| first | assumption | chase)

open PVM JAM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

theorem run_y (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (ω10 : Regs)
    (μ10 : Memory) (C I S : Nat) (hC : C < 65536) (hI : I < 65536) (hS : S < 4294967296)
    (salt : List UInt8) (hsalt : salt.length = 32) (L : Nat)
    (hLdef : (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1 + 33 + 32 = L)
    (a0 : ω10[1] = UInt64.ofNat 4278058264)
    (a1 : ω10[4] = UInt64.ofNat 8)
    (a2 : ω10[5] = UInt64.ofNat 4278058544)
    (a3 : ω10[6] = UInt64.ofNat 4278124544)
    (a4 : ω10[7] = UInt64.ofNat 0)
    (a5 : ω10[8] = UInt64.ofNat 33)
    (a6 : μ10.readN 206512 8 = [0, 0, 0, 0, 32, 40, 3, 0])
    (a7 : μ10.readN 206520 8 = [32, 40, 3, 0, 0, 0, 0, 0])
    (a8 : μ10.readN 206824 8 = [0, 0, 0, 0, 0, 0, 0, 128])
    (a9 : μ10.readN 206832 8 = [0, 0, 0, 0, 32, 0, 0, 0])
    (a10 : μ10.readN 206840 4 = [6, 0, 0, 0])
    (a11 : μ10.readN 206848 4 = [0, 0, 0, 0])
    (a12 : μ10.readN 206880 8 = [0, 0, 0, 0, 0, 0, 0, 4])
    (a13 : μ10.readN 206888 4 = [0, 0, 0, 0])
    (a14 : μ10.readN 4278058312 8 = [65, 0, 0, 0, 0, 0, 0, 0])
    (a15 : ∀ a, 196608 ≤ a → a < 196616 → μ10.writable a = true)
    (a16 : ∀ a, 206512 ≤ a → a < 206520 → μ10.writable a = true)
    (a17 : ∀ a, 206824 ≤ a → a < 206840 → μ10.writable a = true)
    (a18 : ∀ a, 206848 ≤ a → a < 206852 → μ10.writable a = true)
    (a19 : ∀ a, 206880 ≤ a → a < 206888 → μ10.writable a = true)
    (a20 : ∀ a, 206976 ≤ a → a < 206992 → μ10.writable a = true)
    (a21 : ∀ a, 4278057992 ≤ a → a < 4278058264 → μ10.writable a = true)
    (a22 : ∀ a, 206512 ≤ a → a < 206528 → μ10.readable a = true)
    (a23 : ∀ a, 206824 ≤ a → a < 206844 → μ10.readable a = true)
    (a24 : ∀ a, 206848 ≤ a → a < 206852 → μ10.readable a = true)
    (a25 : ∀ a, 206880 ≤ a → a < 206892 → μ10.readable a = true)
    (a26 : ∀ a, 4278057992 ≤ a → a < 4278058016 → μ10.readable a = true)
    (a27 : ∀ a, 4278058024 ≤ a → a < 4278058128 → μ10.readable a = true)
    (a28 : ∀ a, 4278058136 ≤ a → a < 4278058176 → μ10.readable a = true)
    (a29 : ∀ a, 4278058184 ≤ a → a < 4278058200 → μ10.readable a = true)
    (a30 : ∀ a, 4278058224 ≤ a → a < 4278058232 → μ10.readable a = true)
    (a31 : ∀ a, 4278058312 ≤ a → a < 4278058320 → μ10.readable a = true)
    (a32 : μ10.readN 66657 7 = [26, 66, 111, 111, 116, 115, 116])
    (a33 : μ10.readN 66664 8 = [114, 97, 112, 32, 83, 101, 114, 118])
    (a34 : μ10.readN 66672 8 = [105, 99, 101, 32, 82, 101, 102, 105])
    (a35 : μ10.readN 66680 8 = [110, 101, 44, 32, 192, 1, 104, 0])
    (a36 : μ10.readN 71060 4 = [48, 49, 50, 51])
    (a37 : μ10.readN 71064 8 = [52, 53, 54, 55, 56, 57, 97, 98])
    (a38 : μ10.readN 71072 4 = [99, 100, 101, 102])
    (a39 : μ10.readN 77040 8 = [36, 10, 0, 0, 0, 0, 0, 0])
    (a40 : μ10.readN 4278058352 8 = [0, 0, 255, 254, 0, 0, 0, 0])
    (a41 : μ10.readN 4278058368 8 = [152, 0, 0, 0, 0, 0, 0, 0])
    (a42 : μ10.readN 4278058360 8 = Num.encodeLE 8 L)
    (a43 : ∀ a, 206512 ≤ a → a < 206516 → μ10.writable a = true)
    (a44 : ∀ a, 206824 ≤ a → a < 206844 → μ10.writable a = true)
    (a45 : ∀ a, 207008 ≤ a → a < 207036 → μ10.writable a = true)
    (a46 : ∀ a, 207072 ≤ a → a < 207088 → μ10.writable a = true)
    (a47 : ∀ a, 4278057712 ≤ a → a < 4278057720 → μ10.writable a = true)
    (a48 : ∀ a, 4278057728 ≤ a → a < 4278057752 → μ10.writable a = true)
    (a49 : ∀ a, 4278057984 ≤ a → a < 4278058000 → μ10.writable a = true)
    (a50 : ∀ a, 4278058064 ≤ a → a < 4278058088 → μ10.writable a = true)
    (a51 : ∀ a, 4278058104 ≤ a → a < 4278058376 → μ10.writable a = true)
    (a52 : ∀ a, 4278058456 ≤ a → a < 4278058472 → μ10.writable a = true)
    (a53 : ∀ a, 4278058488 ≤ a → a < 4278058496 → μ10.writable a = true)
    (a54 : ∀ a, 4278058544 ≤ a → a < 4278058610 → μ10.writable a = true)
    (a55 : ∀ a, 4278058620 ≤ a → a < 4278058624 → μ10.writable a = true)
    (a56 : ∀ a, 4278058648 ≤ a → a < 4278058664 → μ10.writable a = true)
    (a57 : ∀ a, 66657 ≤ a → a < 66688 → μ10.readable a = true)
    (a58 : ∀ a, 71060 ≤ a → a < 71076 → μ10.readable a = true)
    (a59 : ∀ a, 77040 ≤ a → a < 77048 → μ10.readable a = true)
    (a60 : ∀ a, 206512 ≤ a → a < 206516 → μ10.readable a = true)
    (a61 : ∀ a, 206520 ≤ a → a < 206528 → μ10.readable a = true)
    (a62 : ∀ a, 206884 ≤ a → a < 206888 → μ10.readable a = true)
    (a63 : ∀ a, 206912 ≤ a → a < 206913 → μ10.readable a = true)
    (a64 : ∀ a, 206976 ≤ a → a < 206988 → μ10.readable a = true)
    (a65 : ∀ a, 207076 ≤ a → a < 207084 → μ10.readable a = true)
    (a66 : ∀ a, 4278058064 ≤ a → a < 4278058072 → μ10.readable a = true)
    (a67 : ∀ a, 4278058104 ≤ a → a < 4278058120 → μ10.readable a = true)
    (a68 : ∀ a, 4278058128 ≤ a → a < 4278058376 → μ10.readable a = true)
    (a69 : ∀ a, 4278058488 ≤ a → a < 4278058496 → μ10.readable a = true)
    (a70 : ∀ a, 4278058544 ≤ a → a < 4278058568 → μ10.readable a = true)
    (a71 : ∀ a, 4278058600 ≤ a → a < 4278058604 → μ10.readable a = true)
    (a72 : ∀ a, 4278058620 ≤ a → a < 4278058624 → μ10.readable a = true)
    (a73 : ∀ a, 4278058648 ≤ a → a < 4278058664 → μ10.readable a = true)
    (a74 : JAM.HeapPages μ10 48 1044430 51)
    (a75 : ∀ a, 207008 ≤ a → a < 207037 → μ10.writable a = true)
    (a76 : ∀ a, 4278057744 ≤ a → a < 4278057752 → μ10.readable a = true)
    (a77 : ∀ a, 4278058072 ≤ a → a < 4278058088 → μ10.readable a = true)
    (a78 : ∀ a, 4278058104 ≤ a → a < 4278058376 → μ10.readable a = true)
    (a79 : ∀ a, 207008 ≤ a → a < 207038 → μ10.writable a = true)
    (a80 : ∀ a, 4278057736 ≤ a → a < 4278057752 → μ10.readable a = true)
    (a81 : ∀ a, 4278058064 ≤ a → a < 4278058088 → μ10.readable a = true)
    (a82 : ∀ a, 207008 ≤ a → a < 207039 → μ10.writable a = true)
    (a83 : ∀ a, 207008 ≤ a → a < 207040 → μ10.writable a = true)
    (a84 : ∀ a, 207008 ≤ a → a < 207041 → μ10.writable a = true)
    (a85 : ∀ a, 207008 ≤ a → a < 207042 → μ10.writable a = true)
    (a86 : ∀ a, 4278057736 ≤ a → a < 4278057744 → μ10.readable a = true)
    (a87 : ∀ a, 207008 ≤ a → a < 207043 → μ10.writable a = true)
    (a88 : ∀ a, 196608 ≤ a → a < 196616 → μ10.readable a = true)
    (a89 : μ10.readN 4278058280 8 = Num.encodeLE 8 S)
    (a90 : μ10.readN 4278058288 8 = Num.encodeLE 8 I)
    (a91 : μ10.readN 4278058296 8 = Num.encodeLE 8 C)
    (a92 : μ10.readN 4278058304 8 = Num.encodeLE 8 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1))
    (a93 : μ10.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1) 33 = 0 :: salt)
    (a94 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ10.readable a = true)
    (a95 : ∀ a, 4278057688 ≤ a → a < 4278059008 → μ10.writable a = true)
    (a96 : ∀ a, 196608 ≤ a → a < 208896 → μ10.writable a = true)
    (a97 : μ10.readN 66099 5 = [10, 82, 101, 116, 117])
    (a98 : μ10.readN 66104 8 = [114, 110, 105, 110, 103, 32, 192, 16])
    (a99 : μ10.readN 66112 8 = [32, 105, 110, 116, 111, 32, 97, 99])
    (a100 : μ10.readN 66120 8 = [99, 117, 109, 117, 108, 97, 116, 101])
    (a101 : μ10.readN 66128 1 = [0])
    (a102 : μ10.readN 72826 1 = [93])
    (a103 : μ10.readN 72829 1 = [91])
    (a104 : μ10.readN 196800 4 = [0, 0, 0, 0])
    (a105 : μ10.readN 206528 8 = [0, 0, 0, 0, 0, 0, 0, 0])
    (a106 : μ10.readN 4278058984 8 = [0, 0, 0, 0, 0, 0, 0, 0])
    (a107 : μ10.readN 4278058992 8 = [0, 0, 0, 0, 0, 0, 0, 0])
    (a108 : μ10.readN 4278059000 8 = [0, 0, 255, 255, 0, 0, 0, 0])
    (a109 : ∀ a, 196800 ≤ a → a < 196804 → μ10.writable a = true)
    (a110 : ∀ a, 206528 ≤ a → a < 206536 → μ10.writable a = true)
    (a111 : ∀ a, 206880 ≤ a → a < 206896 → μ10.writable a = true)
    (a112 : ∀ a, 207040 ≤ a → a < 207056 → μ10.writable a = true)
    (a113 : ∀ a, 4278058064 ≤ a → a < 4278058376 → μ10.writable a = true)
    (a114 : ∀ a, 4278058496 ≤ a → a < 4278058504 → μ10.writable a = true)
    (a115 : ∀ a, 4278058544 ≤ a → a < 4278058600 → μ10.writable a = true)
    (a116 : ∀ a, 4278058624 ≤ a → a < 4278058680 → μ10.writable a = true)
    (a117 : ∀ a, 66099 ≤ a → a < 66129 → μ10.readable a = true)
    (a118 : ∀ a, 72826 ≤ a → a < 72827 → μ10.readable a = true)
    (a119 : ∀ a, 72829 ≤ a → a < 72830 → μ10.readable a = true)
    (a120 : ∀ a, 196800 ≤ a → a < 196804 → μ10.readable a = true)
    (a121 : ∀ a, 206520 ≤ a → a < 206536 → μ10.readable a = true)
    (a122 : ∀ a, 206880 ≤ a → a < 206888 → μ10.readable a = true)
    (a123 : ∀ a, 207008 ≤ a → a < 207011 → μ10.readable a = true)
    (a124 : ∀ a, 4278058064 ≤ a → a < 4278058376 → μ10.readable a = true)
    (a125 : ∀ a, 4278058456 ≤ a → a < 4278058472 → μ10.readable a = true)
    (a126 : ∀ a, 4278058544 ≤ a → a < 4278058570 → μ10.readable a = true)
    (a127 : ∀ a, 4278058624 ≤ a → a < 4278058680 → μ10.readable a = true)
    (a128 : ∀ a, 4278058984 ≤ a → a < 4278059008 → μ10.readable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 35130 ω10 μ10 ((∅, []) : RefineCtx) 35202 ω' μ'
      ((∅, []) : RefineCtx) 1500 ∧
      (ω'[1] = UInt64.ofNat 4278058264) ∧
      (ω'[5] = UInt64.ofNat 4278058544) ∧
      (ω'[6] = UInt64.ofNat 33) ∧
      (ω'[7] = UInt64.ofNat 0) ∧
      (μ'.readN 66657 7 = [26, 66, 111, 111, 116, 115, 116]) ∧
      (μ'.readN 66664 8 = [114, 97, 112, 32, 83, 101, 114, 118]) ∧
      (μ'.readN 66672 8 = [105, 99, 101, 32, 82, 101, 102, 105]) ∧
      (μ'.readN 66680 8 = [110, 101, 44, 32, 192, 1, 104, 0]) ∧
      (μ'.readN 71060 4 = [48, 49, 50, 51]) ∧
      (μ'.readN 71064 8 = [52, 53, 54, 55, 56, 57, 97, 98]) ∧
      (μ'.readN 71072 4 = [99, 100, 101, 102]) ∧
      (μ'.readN 77040 8 = [36, 10, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 206512 4 = [128, 40, 3, 0]) ∧
      (μ'.readN 206520 8 = [32, 40, 3, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 206824 8 = [0, 0, 0, 0, 0, 0, 0, 64]) ∧
      (μ'.readN 206832 8 = [0, 0, 0, 0, 32, 0, 0, 0]) ∧
      (μ'.readN 206840 4 = [6, 0, 0, 0]) ∧
      (μ'.readN 206848 4 = [0, 0, 0, 0]) ∧
      (μ'.readN 206884 4 = [7, 0, 0, 0]) ∧
      (μ'.readN 206912 1 = [0]) ∧
      (μ'.readN 206976 8 = [3, 0, 0, 0, 250, 255, 255, 3]) ∧
      (μ'.readN 206984 4 = [0, 0, 0, 0]) ∧
      (μ'.readN 4278058264 8 = [33, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058272 8 = [64, 40, 3, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058352 8 = [0, 0, 255, 254, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058368 8 = [152, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058288 8 = Num.encodeLE 8 I) ∧
      (μ'.readN 4278058360 8 = Num.encodeLE 8 L) ∧
      (μ'.readN 4278058296 8 = Num.encodeLE 8 C) ∧
      (μ'.readN 4278058280 8 = Num.encodeLE 8 S) ∧
      (∀ a, 196608 ≤ a → a < 196616 → μ'.writable a = true) ∧
      (∀ a, 206512 ≤ a → a < 206516 → μ'.writable a = true) ∧
      (∀ a, 206824 ≤ a → a < 206844 → μ'.writable a = true) ∧
      (∀ a, 206848 ≤ a → a < 206852 → μ'.writable a = true) ∧
      (∀ a, 206976 ≤ a → a < 206992 → μ'.writable a = true) ∧
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
      (∀ a, 206824 ≤ a → a < 206844 → μ'.readable a = true) ∧
      (∀ a, 206848 ≤ a → a < 206852 → μ'.readable a = true) ∧
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
      (μ'.readN 66099 5 = [10, 82, 101, 116, 117]) ∧
      (μ'.readN 66104 8 = [114, 110, 105, 110, 103, 32, 192, 16]) ∧
      (μ'.readN 66112 8 = [32, 105, 110, 116, 111, 32, 97, 99]) ∧
      (μ'.readN 66120 8 = [99, 117, 109, 117, 108, 97, 116, 101]) ∧
      (μ'.readN 66128 1 = [0]) ∧
      (μ'.readN 72826 1 = [93]) ∧
      (μ'.readN 72829 1 = [91]) ∧
      (μ'.readN 196800 4 = [0, 0, 0, 0]) ∧
      (μ'.readN 206528 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 206880 8 = [0, 0, 0, 0, 7, 0, 0, 0]) ∧
      (μ'.readN 4278058984 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278058992 8 = [0, 0, 0, 0, 0, 0, 0, 0]) ∧
      (μ'.readN 4278059000 8 = [0, 0, 255, 255, 0, 0, 0, 0]) ∧
      (∀ a, 196800 ≤ a → a < 196804 → μ'.writable a = true) ∧
      (∀ a, 206528 ≤ a → a < 206536 → μ'.writable a = true) ∧
      (∀ a, 206824 ≤ a → a < 206840 → μ'.writable a = true) ∧
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
      (∀ a, 4278058984 ≤ a → a < 4278059008 → μ'.readable a = true) ∧
      (∀ a, 4278057688 ≤ a → a < 4278059008 → μ'.writable a = true) ∧
      (∀ a, 196608 ≤ a → a < 208896 → μ'.writable a = true) := by
  have hwC := encodeNat_len_le3 C hC
  have hwI := encodeNat_len_le3 I hI
  have hwS := encodeNat_len_le5 S hS
  chase_prep at a6 a7 a8 a9 a10 a11 a12 a13 a14 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a97 a98 a99 a100 a101 a102 a103 a104 a105 a106 a107 a108
  refine (fun hG => ?_) (GlueY.run p P env ω10 μ10 ((∅, []) : RefineCtx) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · obtain ⟨ω11, μ11, run11, ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12⟩, ym, yfr, yrd, ywr⟩ := hG
    have hrd11 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ11.readable a = true := fun a h1 h2 => by
      rw [yrd]; exact a94 a h1 h2
    have hwr11 : ∀ a, 4278057688 ≤ a → a < 4278059008 → μ11.writable a = true := fun a h1 h2 => by
      rw [ywr]; exact a95 a h1 h2
    have hhp11 : ∀ a, 206912 ≤ a → a < 206912 + 33 → μ11.writable a = true := fun a h1 h2 => by
      rw [ywr]; exact a96 a (by omega) (by omega)
    -- the 33 octets, to the heap
    obtain ⟨ω12, μ12, run12, k0, k1, k5, k6, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩ :=
      read_big (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω11 μ11 90 3635 4278058168
        4278058304 206912 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length +
          (Blob.encodeNat S).length + 1)
        (L - (Blob.encodeNat C).length - (Blob.encodeNat I).length - (Blob.encodeNat S).length - 1) 33
        y0 y1 y7 y8 y9 (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_44]) bs_3635
        (by decide) (by decide) (by decide) (by omega) (by decide) (by omega) (by omega) (by decide)
        (by omega) (by omega) (by decide) (by omega)
        (fun a h1 h2 => hwr11 a (by omega) (by omega)) (fun a h1 h2 => hwr11 a (by omega) (by omega))
        hhp11 (fun a h1 h2 => hrd11 a (by omega) (by omega))
        (by
          rw [Memory.readN_congr (fun j hj => yfr _ (by simp only [Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt]; omega))]; exact a92)
        (by
          rw [Memory.readN_congr (fun j hj => yfr _ (by simp only [Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt]; omega)), show L - (Blob.encodeNat C).length - (Blob.encodeNat I).length -
            (Blob.encodeNat S).length - 1 = 65 by omega]; chase)
    refine (fun hG2 => ?_) (GlueY2.run p P env ω12 μ12 ((∅, []) : RefineCtx) L ⟨by omega, by omega⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · obtain ⟨ω13, μ13, run13, ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12⟩, zm, zfr, zrd, zwr⟩ := hG2
      -- the hash
      obtain ⟨ω14, μ14, run14, j0, j1, j5, j6, j7, jR0, jR8, jbuf, jfr, jrd, jwr⟩ :=
        read_big (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω13 μ13 1644 35202 4278058264
          4278058304 4278058320 (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length +
            (Blob.encodeNat S).length + 1 + 33)
          (L - (Blob.encodeNat C).length - (Blob.encodeNat I).length - (Blob.encodeNat S).length - 1 - 33) 32
          z0 z1 z7 z8 z9 (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_821]) bs_35202
          (by decide) (by decide) (by decide) (by omega) (by decide) (by omega) (by omega) (by decide)
          (by omega) (by omega) (by decide) (by omega)
          (fun a h1 h2 => by rw [zwr, kwr]; exact hwr11 a (by omega) (by omega))
          (fun a h1 h2 => by rw [zwr, kwr]; exact hwr11 a (by omega) (by omega))
          (fun a h1 h2 => by rw [zwr, kwr]; exact hwr11 a (by omega) (by omega))
          (fun a h1 h2 => by rw [zrd, krd]; exact hrd11 a (by omega) (by omega))
          (by
            rw [Memory.readN_congr (fun j hj => zfr _ (by simp only [Bool.and_eq_true, decide_eq_true_eq,
              Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt]; omega)), kR0])
          (by
            rw [Memory.readN_congr (fun j hj => zfr _ (by simp only [Bool.and_eq_true, decide_eq_true_eq,
              Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt]; omega)), kR8, Nat.sub_sub])
      have c14 : ∀ a, a < 4294967296 → 4278058280 ≤ a → a < 4278058304 ∨ (4278058360 ≤ a ∧ a < 4278058368) →
          μ14.read a = μ10.read a := fun a h0 h1 h2 =>
        (jfr a h0 (by omega) (by omega) (by omega)).trans ((zfr a (by simp only [Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt]; omega)).trans
          ((kfr a h0 (by omega) (by omega) (by omega)).trans (yfr a (by simp only [Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt]; omega))))
      have q14S : μ14.readN 4278058280 8 = Num.encodeLE 8 S := by
        rw [Memory.readN_congr (fun j hj => c14 _ (by omega) (by omega) (by omega))]; exact a89
      have q14I : μ14.readN 4278058288 8 = Num.encodeLE 8 I := by
        rw [Memory.readN_congr (fun j hj => c14 _ (by omega) (by omega) (by omega))]; exact a90
      have q14C : μ14.readN 4278058296 8 = Num.encodeLE 8 C := by
        rw [Memory.readN_congr (fun j hj => c14 _ (by omega) (by omega) (by omega))]; exact a91
      have q14L : μ14.readN 4278058360 8 = Num.encodeLE 8 L := by
        rw [Memory.readN_congr (fun j hj => c14 _ (by omega) (by omega) (by omega))]; exact a42
      have q14P : μ14.readN 206912 1 = [0] := by
        rw [Memory.readN_congr (fun j hj => (jfr _ (by omega) (by omega) (by omega) (by omega)).trans
          (zfr _ (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
            not_and, Nat.not_lt]; omega)))]
        rw [← readN_take μ12 206912 33 1 (by omega), kbuf, readN_take _ _ 33 1 (by omega)]
        rw [Memory.readN_congr (fun j hj => yfr _ (by simp only [Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt]; omega))]
        rw [← readN_take μ10 _ 33 1 (by omega), a93]
        rfl
      have hpg14 : JAM.HeapPages μ14 48 1044430 51 :=
        NoInstrArgs.heapPages_of_writable (fun x => by rw [jwr, zwr, kwr, ywr]) a74
      refine ⟨ω14, μ14, (run11.trans (run12.trans (run13.trans run14))).mono
        (by omega), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals tail_facts
    all_goals tail_facts
  all_goals tail_facts

end Services.Bootstrap.NoInstrHead
