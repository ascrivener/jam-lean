import JAM.Sha512
import JAM.Trie
import JAM.Decode
import JAM.Theorems.LoopRel

/-!
# Checked indexing in the spec: the new definitions equal the old ones

The spec definitions no longer use unchecked indexing (`a[i]!`, `ByteArray.get!`):
each access is now proved in bounds, or reads through `getD` where the definition's own invariant
makes the default unreachable. This file keeps each changed definition's earlier form verbatim
(namespace `JAM.Theorems.CheckedIndex.Old`) and proves it equal to the current one, so the change
alters no value.
-/

namespace JAM.Theorems.CheckedIndex
open JAM.Theorems

namespace Old

/-! ## SHA-512 (`JAM.Sha512`), before the state became `Vector`s -/

namespace Sha512
/-- The old `K` and `H0` were these arrays written out (`#[…]`); the current ones are the same literals as `#v[…]`. -/
def K : Array UInt64 := JAM.Sha512.K.toArray
def H0 : Array UInt64 := JAM.Sha512.H0.toArray
open JAM.Sha512 (rotr)


/-- The compression function on one 128-octet block starting at `off` (FIPS 180-4 §6.4.2). -/
def compress (h : Array UInt64) (m : ByteArray) (off : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := Array.replicate 80 0
  for t in [0:16] do
    let mut x : UInt64 := 0
    for j in [0:8] do
      x := (x <<< 8) ||| (m.get! (off + 8 * t + j)).toUInt64
    w := w.set! t x
  for t in [16:80] do
    let s0 := rotr w[t-15]! 1 ^^^ rotr w[t-15]! 8 ^^^ (w[t-15]! >>> 7)
    let s1 := rotr w[t-2]! 19 ^^^ rotr w[t-2]! 61 ^^^ (w[t-2]! >>> 6)
    w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for t in [0:80] do
    let S1 := rotr e 14 ^^^ rotr e 18 ^^^ rotr e 41
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := hh + S1 + ch + K[t]! + w[t]!
    let S0 := rotr a 28 ^^^ rotr a 34 ^^^ rotr a 39
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- SHA-512 of an octet sequence, padded as in FIPS 180-4 §5.1.2. -/
def hash (msg : List UInt8) : List UInt8 := Id.run do
  let len := msg.length
  let padLen := (128 - (len + 17) % 128) % 128
  let lenBytes := (List.range 16).map fun i => UInt8.ofNat ((8 * len) / 2 ^ (8 * (15 - i)) % 256)
  let m : ByteArray := ⟨(msg ++ [0x80] ++ List.replicate padLen 0 ++ lenBytes).toArray⟩
  let mut h := H0
  for i in [0:m.size / 128] do
    h := compress h m (128 * i)
  return h.toList.flatMap fun x => (List.range 8).map fun j => (x >>> (8 * (7 - j)).toUInt64).toUInt8

end Sha512

/-! ## State keys (`JAM.Trie`) -/

namespace Trie
open JAM.Trie (n4)

def keyOfService (i s : Nat) : List UInt8 :=
  let n := n4 s
  [UInt8.ofNat i, n[0]!, 0, n[1]!, 0, n[2]!, 0, n[3]!] ++ List.replicate 23 0

def keyOfServiceData (s : Nat) (h : List UInt8) : List UInt8 :=
  let n := n4 s
  let a := (Blake2b.hash256 ⟨h.toArray⟩).toList
  [n[0]!, a[0]!, n[1]!, a[1]!, n[2]!, a[2]!, n[3]!, a[3]!] ++ (a.drop 4).take 23

def keyOfServiceHash (s : Nat) (a : List UInt8) : List UInt8 :=
  let n := n4 s
  [n[0]!, a[0]!, n[1]!, a[1]!, n[2]!, a[2]!, n[3]!, a[3]!] ++ (a.drop 4).take 23

end Trie

/-! ## One octet (`JAM.Decoder.byte`) -/

def Decoder.byte : JAM.Decoder UInt8 := do
  let b ← JAM.Decoder.bytes 1
  return b.get! 0

end Old

/-! ## SHA-512 -/

open JAM.Sha512 (rotr K H0 compress)

theorem sha512_compress_eq_old (h : Vector UInt64 8) (m : ByteArray) (off : Nat) (hoff : off + 128 ≤ m.size) :
    Old.Sha512.compress h.toArray m off = (compress h m off hoff).toArray := by
  unfold Old.Sha512.compress compress
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
  have getB : ∀ k (hk : k < m.size), m.get! k = m[k] := by
    intro k hk; simp [ByteArray.get!, ByteArray.getElem_eq_getElem_data, getElem!_pos, hk]
  have getV : ∀ (v : Vector UInt64 80) k (hk : k < 80), v.toArray[k]! = v[k] := by
    intro v k hk; simp [getElem!_pos, hk]
  refine LoopRel.bind_rel (fun (w : Array UInt64) (v : Vector UInt64 80) => w = v.toArray) (fun (a : Array UInt64) (b : Vector UInt64 8) => a = b.toArray) ?_ ?_
  · refine LoopRel.forIn_forIn' (fun (w : Array UInt64) (v : Vector UInt64 80) => w = v.toArray) _ _ _ _ (by simp) ?_
    rintro t ht w v rfl
    refine LoopRel.bind_rel Eq (LoopRel.StepRel _) ?_ ?_
    · refine LoopRel.forIn_forIn' Eq _ _ _ _ rfl ?_
      rintro j hj x _ rfl
      simp at ht hj
      simp only [LoopRel.StepRel, Id.run, pure]
      rw [getB _ (by omega)]
    · rintro x _ rfl
      simp only [LoopRel.StepRel, Id.run, pure]
      simp at ht
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, show t < 80 by omega]
  rintro _ v rfl
  refine LoopRel.bind_rel (fun (w : Array UInt64) (v : Vector UInt64 80) => w = v.toArray) (fun (a : Array UInt64) (b : Vector UInt64 8) => a = b.toArray) ?_ ?_
  · refine LoopRel.forIn_forIn' (fun (w : Array UInt64) (v : Vector UInt64 80) => w = v.toArray) _ _ _ _ rfl ?_
    rintro t ht w v rfl
    simp at ht
    simp only [LoopRel.StepRel, Id.run, pure]
    rw [getV _ _ (by omega), getV _ _ (by omega), getV _ _ (by omega), getV _ _ (by omega)]
    simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, show t < 80 by omega]
  rintro _ v rfl
  refine LoopRel.bind_rel Eq (fun (a : Array UInt64) (b : Vector UInt64 8) => a = b.toArray) ?_ ?_
  · refine LoopRel.forIn_forIn' Eq _ _ _ _ (by simp [getElem!_pos]) ?_
    rintro t ht x _ rfl
    simp at ht
    simp only [LoopRel.StepRel, Id.run, pure]
    rw [getV _ _ ht]
    simp [Old.Sha512.K, getElem!_pos, ht]
  rintro x _ rfl
  simp [getElem!_pos]

theorem sha512_hash_eq_old (msg : List UInt8) : Old.Sha512.hash msg = JAM.Sha512.hash msg := by
  unfold Old.Sha512.hash JAM.Sha512.hash
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine LoopRel.bind_rel (fun (a : Array UInt64) (b : Vector UInt64 8) => a = b.toArray) Eq ?_ ?_
  · refine LoopRel.forIn_forIn' (fun (a : Array UInt64) (b : Vector UInt64 8) => a = b.toArray) _ _ _ _ rfl ?_
    rintro i hi a v rfl
    simp only [LoopRel.StepRel, Id.run, pure]
    exact sha512_compress_eq_old ..
  rintro _ v rfl
  rfl

/-! ## State keys -/

theorem n4_getElem! (s i : Nat) (hi : i < 4) :
    (Trie.n4 s)[i]! = (Trie.n4 s)[i]'(by rw [Trie.length_n4]; exact hi) := by
  simp [getElem!_pos, Trie.length_n4, hi]

theorem list_getElem!_eq_getD (a : List UInt8) (i : Nat) : a[i]! = a.getD i 0 := by
  simp [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]; rfl

theorem keyOfService_eq_old (i s : Nat) : Old.Trie.keyOfService i s = Trie.keyOfService i s := by
  simp only [Old.Trie.keyOfService, Trie.keyOfService, n4_getElem! s _ (by decide : 0 < 4),
    n4_getElem! s _ (by decide : 1 < 4), n4_getElem! s _ (by decide : 2 < 4), n4_getElem! s _ (by decide : 3 < 4)]

theorem keyOfServiceHash_eq_old (s : Nat) (a : List UInt8) :
    Old.Trie.keyOfServiceHash s a = Trie.keyOfServiceHash s a := by
  simp only [Old.Trie.keyOfServiceHash, Trie.keyOfServiceHash, n4_getElem! s _ (by decide : 0 < 4),
    n4_getElem! s _ (by decide : 1 < 4), n4_getElem! s _ (by decide : 2 < 4), n4_getElem! s _ (by decide : 3 < 4),
    list_getElem!_eq_getD]

theorem keyOfServiceData_eq_old (s : Nat) (h : List UInt8) :
    Old.Trie.keyOfServiceData s h = Trie.keyOfServiceData s h := by
  rw [Trie.keyOfServiceData, ← keyOfServiceHash_eq_old]; rfl

/-! ## One octet -/

theorem byte_eq_old : Old.Decoder.byte = JAM.Decoder.byte := by
  have hthrow : ∀ {α β : Type} (e : String) (k : α → JAM.Decoder β),
      ((throw e : JAM.Decoder α) >>= k) = throw e := fun _ _ => rfl
  simp only [Old.Decoder.byte, JAM.Decoder.byte, JAM.Decoder.bytes, bind_assoc]
  refine congrArg (read >>= ·) (funext fun bs => congrArg (get >>= ·) (funext fun pos => ?_))
  by_cases h : pos + 1 ≤ bs.size
  · simp only [h, ite_true, dite_true, bind_assoc, pure_bind]
    congr 1; funext _; congr 1
    have h' : pos + 1 ≤ bs.data.size := h
    have h1 : 0 < (bs.data.extract pos (pos + 1)).size := by rw [Array.size_extract]; omega
    simp only [ByteArray.get!, ByteArray.getElem_eq_getElem_data, ByteArray.data_extract]
    rw [getElem!_pos (bs.data.extract pos (pos + 1)) 0 h1, Array.getElem_extract]; rfl
  · simp only [h, ite_false, dite_false, JAM.Decoder.fail, bind_assoc, hthrow]

end JAM.Theorems.CheckedIndex
