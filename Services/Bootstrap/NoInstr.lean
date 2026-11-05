import Services.Bootstrap.NoInstrArgs
import Services.Bootstrap.NoInstrHead
import Services.Bootstrap.NoInstrTail1
import Services.Bootstrap.NoInstrTail2
import Services.Bootstrap.NoInstrTail3
import Services.Bootstrap.NoInstrTail4
import Services.Bootstrap.NoInstrTail5
import Services.Bootstrap.NoInstrTail6
import Services.Bootstrap.NoInstrTail7
import Services.Bootstrap.NoInstrTail8
import Services.Bootstrap.PsiREmpty
import Services.Witness.Lift

/-!
# Bootstrap's refine on an empty instruction list, end to end

The payload ℰ(`Instructions { instructions: [], salt }`) = [0] ⌢ salt (a compact length 0, then
the 32-octet salt). From Y's state: `NoInstrArgs.run_args` (the prefix, the parameters and the
decodes of c, i, s and |y|), `NoInstrHead.run_y` (the payload's copy and the hash's read) and the
tail for s's number of hex digits (`NoInstrTail1` … `NoInstrTail8`), to the halt at 6373 with
the output ℰ(`BootstrapWorkOutput { instructions: [], work_item_index: i }`) = [0] ⌢ ℰ₂(i). Then
Ψ_M (GP §A.8) and Ψ_R (GP eq. `refinvocation`).
-/

namespace Services.Bootstrap.NoInstr

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Prefix

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

theorem run_noinstr (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (hμ : StartMem μ) (C I S : Nat) (h : List UInt8) (hC : C < 65536) (hI : I < 65536)
    (hS : S < 4294967296) (salt : List UInt8) (hsalt : salt.length = 32) (hh : h.length = 32)
    (hmem : μ.readN 4278124544 (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat 33 ++ (0 :: salt) ++ h).length = Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat 33 ++ (0 :: salt) ++ h)
    (hrd : ∀ j, 4278124544 ≤ j → j < 4278124544 + (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat 33 ++ (0 :: salt) ++ h).length → μ.readable j = true) :
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 (initRegs (Blob.encodeNat C ++ Blob.encodeNat I ++
      Blob.encodeNat S ++ Blob.encodeNat 33 ++ (0 :: salt) ++ h).length) μ ((∅, []) : RefineCtx) 6373
      ω' μ' x' 11000 ∧
      ω'[0] = UInt64.ofNat 4294901760 ∧ ω'[7] = UInt64.ofNat 207008 ∧ ω'[8] = UInt64.ofNat 3 ∧
      μ'.readN 207008 3 = 0 :: Num.encodeLE 2 I ∧ (∀ a, 207008 ≤ a → a < 207011 → μ'.readable a = true) := by
  have hwC := encodeNat_len_le3 C hC
  have hwI := encodeNat_len_le3 I hI
  have hwS := encodeNat_len_le5 S hS
  have hw33 : (Blob.encodeNat 33).length = 1 := by decide
  have hlen : (Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++ Blob.encodeNat 33 ++ (0 :: salt) ++
      h).length = (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1 + 33 + 32 := by
    simp [hh, hw33, hsalt]; omega
  rw [hlen] at hmem hrd ⊢
  generalize hLdef : (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length + 1 + 33 + 32
    = L at hmem hrd ⊢
  obtain ⟨ω1, μ1, run1, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, a77, a78, a79, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90, a91, a92, a93, a94, a95, a96, a97, a98, a99, a100, a101, a102, a103, a104, a105, a106, a107, a108, a109, a110, a111, a112, a113, a114, a115, a116, a117, a118, a119, a120, a121, a122, a123, a124, a125, a126, a127, a128⟩ :=
    NoInstrArgs.run_args p P env henv hpar μ hμ C I S h hC hI hS salt hsalt hh L hLdef hmem hrd
  obtain ⟨ω2, μ2, run2, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90, b91, b92, b93, b94, b95, b96, b97, b98, b99, b100, b101, b102, b103, b104, b105, b106, b107, b108, b109, b110, b111, b112, b113, b114, b115, b116⟩ :=
    NoInstrHead.run_y p P env henv hpar ω1 μ1 C I S hC hI hS salt hsalt L hLdef a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 a65 a66 a67 a68 a69 a70 a71 a72 a73 a74 a75 a76 a77 a78 a79 a80 a81 a82 a83 a84 a85 a86 a87 a88 a89 a90 a91 a92 a93 a94 a95 a96 a97 a98 a99 a100 a101 a102 a103 a104 a105 a106 a107 a108 a109 a110 a111 a112 a113 a114 a115 a116 a117 a118 a119 a120 a121 a122 a123 a124 a125 a126 a127 a128
  have : (S < 16) ∨ (16 ≤ S ∧ S < 256) ∨ (256 ≤ S ∧ S < 4096) ∨ (4096 ≤ S ∧ S < 65536) ∨ (65536 ≤ S ∧ S < 1048576) ∨ (1048576 ≤ S ∧ S < 16777216) ∨ (16777216 ≤ S ∧ S < 268435456) ∨ (268435456 ≤ S) := by omega
  rcases this with hd | hd | hd | hd | hd | hd | hd | hd
  · obtain ⟨ω3, μ3, run3, o0, o7, o8, oo, ord⟩ := NoInstrTail1.run_tail p P env henv hpar ω2 μ2 C I S hC hI
      ⟨by omega, by omega⟩ L ⟨by omega, by omega⟩ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 b83 b84 b85 b86 b87 b88 b89 b90 b91 b92 b93 b94 b95 b96 b97 b98 b99 b100 b101 b102 b103 b104 b105 b106 b107 b108 b109 b110 b111 b112 b113 b114 b115 b116
    exact ⟨ω3, μ3, _, (run1.trans (run2.trans run3)).mono (by omega), o0, o7, o8, oo, ord⟩
  · obtain ⟨ω3, μ3, run3, o0, o7, o8, oo, ord⟩ := NoInstrTail2.run_tail p P env henv hpar ω2 μ2 C I S hC hI
      ⟨by omega, by omega⟩ L ⟨by omega, by omega⟩ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 b83 b84 b85 b86 b87 b88 b89 b90 b91 b92 b93 b94 b95 b96 b97 b98 b99 b100 b101 b102 b103 b104 b105 b106 b107 b108 b109 b110 b111 b112 b113 b114 b115 b116
    exact ⟨ω3, μ3, _, (run1.trans (run2.trans run3)).mono (by omega), o0, o7, o8, oo, ord⟩
  · obtain ⟨ω3, μ3, run3, o0, o7, o8, oo, ord⟩ := NoInstrTail3.run_tail p P env henv hpar ω2 μ2 C I S hC hI
      ⟨by omega, by omega⟩ L ⟨by omega, by omega⟩ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 b83 b84 b85 b86 b87 b88 b89 b90 b91 b92 b93 b94 b95 b96 b97 b98 b99 b100 b101 b102 b103 b104 b105 b106 b107 b108 b109 b110 b111 b112 b113 b114 b115 b116
    exact ⟨ω3, μ3, _, (run1.trans (run2.trans run3)).mono (by omega), o0, o7, o8, oo, ord⟩
  · obtain ⟨ω3, μ3, run3, o0, o7, o8, oo, ord⟩ := NoInstrTail4.run_tail p P env henv hpar ω2 μ2 C I S hC hI
      ⟨by omega, by omega⟩ L ⟨by omega, by omega⟩ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 b83 b84 b85 b86 b87 b88 b89 b90 b91 b92 b93 b94 b95 b96 b97 b98 b99 b100 b101 b102 b103 b104 b105 b106 b107 b108 b109 b110 b111 b112 b113 b114 b115 b116
    exact ⟨ω3, μ3, _, (run1.trans (run2.trans run3)).mono (by omega), o0, o7, o8, oo, ord⟩
  · obtain ⟨ω3, μ3, run3, o0, o7, o8, oo, ord⟩ := NoInstrTail5.run_tail p P env henv hpar ω2 μ2 C I S hC hI
      ⟨by omega, by omega⟩ L ⟨by omega, by omega⟩ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 b83 b84 b85 b86 b87 b88 b89 b90 b91 b92 b93 b94 b95 b96 b97 b98 b99 b100 b101 b102 b103 b104 b105 b106 b107 b108 b109 b110 b111 b112 b113 b114 b115 b116
    exact ⟨ω3, μ3, _, (run1.trans (run2.trans run3)).mono (by omega), o0, o7, o8, oo, ord⟩
  · obtain ⟨ω3, μ3, run3, o0, o7, o8, oo, ord⟩ := NoInstrTail6.run_tail p P env henv hpar ω2 μ2 C I S hC hI
      ⟨by omega, by omega⟩ L ⟨by omega, by omega⟩ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 b83 b84 b85 b86 b87 b88 b89 b90 b91 b92 b93 b94 b95 b96 b97 b98 b99 b100 b101 b102 b103 b104 b105 b106 b107 b108 b109 b110 b111 b112 b113 b114 b115 b116
    exact ⟨ω3, μ3, _, (run1.trans (run2.trans run3)).mono (by omega), o0, o7, o8, oo, ord⟩
  · obtain ⟨ω3, μ3, run3, o0, o7, o8, oo, ord⟩ := NoInstrTail7.run_tail p P env henv hpar ω2 μ2 C I S hC hI
      ⟨by omega, by omega⟩ L ⟨by omega, by omega⟩ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 b83 b84 b85 b86 b87 b88 b89 b90 b91 b92 b93 b94 b95 b96 b97 b98 b99 b100 b101 b102 b103 b104 b105 b106 b107 b108 b109 b110 b111 b112 b113 b114 b115 b116
    exact ⟨ω3, μ3, _, (run1.trans (run2.trans run3)).mono (by omega), o0, o7, o8, oo, ord⟩
  · obtain ⟨ω3, μ3, run3, o0, o7, o8, oo, ord⟩ := NoInstrTail8.run_tail p P env henv hpar ω2 μ2 C I S hC hI
      ⟨by omega, by omega⟩ L ⟨by omega, by omega⟩ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 b64 b65 b66 b67 b68 b69 b70 b71 b72 b73 b74 b75 b76 b77 b78 b79 b80 b81 b82 b83 b84 b85 b86 b87 b88 b89 b90 b91 b92 b93 b94 b95 b96 b97 b98 b99 b100 b101 b102 b103 b104 b105 b106 b107 b108 b109 b110 b111 b112 b113 b114 b115 b116
    exact ⟨ω3, μ3, _, (run1.trans (run2.trans run3)).mono (by omega), o0, o7, o8, oo, ord⟩

/-- **The halting step** at 6373: `jump_ind ω₀` with ω₀ = 2^32 − 2^16 halts (GP §A.5.1). -/
theorem halt_6373 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 4294901760) : FreeExit p 6373 ω μ .halt ω μ := by
  have hd := d_6373 (p := p) (P := P)
  have hs : P.freeStep 6373 ω μ = (.halt, 6373, ω, μ) := by
    have h0' : ω.get 0 = UInt64.ofNat 4294901760 := h0
    simp [Program.freeStep, hd.2.1, Program.exec, h0', Program.djump, Program.finalState,
      memoryException, two32]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  simpa using this

open Services.Bootstrap.PsiREmpty in
/-- **Bootstrap's refine returns the empty instruction list it is given** (GP eq. `refinvocation`).
    For a work item whose service's code, looked up historically, is a blob with the deployed layout
    that passes `checkCode` for bootstrap's code facts (`lake build bootstrapcheck` checks both of
    the vendored blob) and the deployed heap bounds, refined with the full-chain parameters: for
    every core index c < 2^16, item index i < 2^16, service id < 2^32 and 32-octet salt, with the
    payload ℰ(`Instructions { instructions: [], salt }`) = [0] ⌢ salt, Ψ_R's result is
    ℰ(`BootstrapWorkOutput { instructions: [], work_item_index: i }`) = [0] ⌢ ℰ₂(i), or ∞. -/
theorem psiR_noinstr (params : Params) (hpar : params = Params.full) (d : Accounts) (c i : Nat)
    (p : WorkPackage) (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat)
    (w : WorkItem) (hw : p.items[i]? = some w) (l : List UInt8)
    (hl : (d.get? w.service).bind (fun a => a.historicalLookup p.context.lookupAnchorSlot
      w.codeHash.toList) = some l)
    (hsize : l.length ≤ Constants.Cmaxservicecodesize) (code : ByteArray)
    (hcode : splitMetadata l = some code) (jb : JamBlob) (hjb : JamBlob.parse? code = some jb)
    (hlay : layoutOk jb = true) (hcc : checkCode jb.code facts = true)
    (hheap : heapBounds code = (48, 1044430)) (hc : c < 65536) (hi : i < 65536)
    (hs : w.service < 4294967296) (salt : List UInt8) (hsalt : salt.length = 32)
    (hy : w.payload.toList = 0 :: salt) :
    (psiR params d c i p r imports extrinsics off).result = .ok ⟨(0 :: Num.encodeLE 2 i).toArray⟩ ∨
      (psiR params d c i p r imports extrinsics off).result = .err .outOfGas := by
  obtain ⟨P, hP⟩ := checkCode_sound hcc
  haveI : HasCode jb.code P := ⟨hP⟩
  simp only [psiR, hw, hl]
  rw [ite_eq_right (by omega)]
  simp only [hcode]
  generalize hE : RefineHost.Env.mk params w.service d p.context.lookupAnchorSlot code off
    (FetchContext.mk params (some p) (some (List.replicate 32 0)) (some r) (some i) (some imports)
      (some extrinsics) none) = env
  have hcodeE : env.code = code := by rw [← hE]
  have hparE : env.fetch.params = params := by rw [← hE]
  generalize hA : (⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat w.service ++ Codec.var w.payload ++
    (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).toArray⟩ : ByteArray) = a
  have hlist : a.toList = Blob.encodeNat c ++ Blob.encodeNat i ++ Blob.encodeNat w.service ++
      Blob.encodeNat 33 ++ (0 :: salt) ++ (Blake2b.hash256 ⟨p.encode.toArray⟩).toList := by
    have h33 : w.payload.toList.length = 33 := by rw [hy]; simp [hsalt]
    rw [← hA]
    simp only [Codec.var, Codec.nat, ← ByteArray.length_toList' w.payload, h33, ← hy, List.append_assoc]
    rw [ByteArray.toList_eq_data]
  have hasize : a.size = (Blob.encodeNat c ++ Blob.encodeNat i ++ Blob.encodeNat w.service ++
      Blob.encodeNat 33 ++ (0 :: salt) ++ (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).length := by
    rw [← hlist, ByteArray.length_toList']
  have hwC := encodeNat_len_le3 c hc
  have hwI := encodeNat_len_le3 i hi
  have hwS := encodeNat_len_le5 w.service hs
  have hw0 : (Blob.encodeNat 33).length = 1 := by decide
  have hh := hash256_length ⟨p.encode.toArray⟩
  have ha : a.size ≤ inputSize := by
    rw [hasize]; simp only [List.length_append, List.length_cons, hsalt, hh, hw0, inputSize]; omega
  have hSM := startMem_initial jb a hlay ha
  simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hlay
  obtain ⟨⟨⟨⟨⟨hro, hrw⟩, hheapP⟩, hstack⟩, _⟩, _⟩ := hlay
  have hY : standardInit code a = some (jb.code, initialRegs a, initialMemory jb a) := by
    have hfit : ¬(5 * zoneSize + roundZone jb.ro.size + roundZone (jb.rw.size + jb.heapPages * pageSize) +
        roundZone jb.stackSize + inputSize > 2 ^ 32) := by
      rw [hro, hrw, hheapP, hstack]; decide
    unfold standardInit validJamBlob?
    rw [ite_eq_right (by omega), hjb, Option.bind_some, ite_eq_right hfit]
    rfl
  have hrs : rwStart jb = 196608 := by simp [rwStart, hro, roundZone, zoneSize]
  have hmem := initialMemory_readN_args jb a (by simp [roStart, zoneSize, hro, two32])
    (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)
  rw [hlist, hasize] at hmem
  have hrun := run_noinstr jb.code P env (by rw [hcodeE, hheap]) (by rw [hparE, hpar])
    (initialMemory jb a) hSM c i w.service (Blake2b.hash256 ⟨p.encode.toArray⟩).toList hc hi hs salt hsalt hh
    (by simpa [argStart, zoneSize, inputSize] using hmem)
    (fun j h1 h2 => initialMemory_readable_args jb a j (by simp [argStart, zoneSize, inputSize]; omega)
      (by rw [hasize]; simp [argStart, zoneSize, inputSize] at h2 ⊢; omega))
  rw [← hasize, ← initRegs_eq] at hrun
  obtain ⟨ω', μ', x', hsteps, h0, h7, h8, hout, hrdo⟩ := hrun
  have hexit : FreeRunH jb.code (refineContract env) 6373 ω' μ' x' .halt ω' μ' x' :=
    .exit (FreeRun.exit (halt_6373 (P := P) ω' μ' h0)) (by simp)
  rcases psiM_of_freeRunH code 0 (UInt64.ofNat w.refineGasLimit) a ((∅, []) : RefineCtx) _
      (refineHostFn_gasNonIncreasing env) (refineContract env) (refineContract_pins env) hY
      (hsteps.run hexit) with h | h
  · right
    cases hm : (psiM code 0 (UInt64.ofNat w.refineGasLimit) a (toHostFn (RefineHost.dispatch env))
      ((∅, []) : RefineCtx)).2.1 <;> simp_all [InvOutput.isOog, InvOutput.toWorkResult]
  · left
    have h7' : (ω'.get 7).toNat = 207008 := by rw [show ω'.get 7 = ω'[7] from rfl, h7]; rfl
    have h8' : (ω'.get 8).toNat = 3 := by rw [show ω'.get 8 = ω'[8] from rfl, h8]; rfl
    have hrr : μ'.rangeReadable 207008 3 = true :=
      Services.Witness.rangeReadable_of (fun j h1 h2 => hrdo j h1 h2) (by decide)
    have hP : (psiM code 0 (UInt64.ofNat w.refineGasLimit) a (toHostFn (RefineHost.dispatch env))
        ((∅, []) : RefineCtx)).2.1 = .ok ⟨(0 :: Num.encodeLE 2 i).toArray⟩ := by
      rw [show (psiM code 0 (UInt64.ofNat w.refineGasLimit) a (toHostFn (RefineHost.dispatch env))
        ((∅, []) : RefineCtx)).2.1 = (freeOutput .halt ω' μ') from congrArg Prod.fst h]
      simp [freeOutput, h7', h8', hrr, hout]
    rw [hP]

end Services.Bootstrap.NoInstr
