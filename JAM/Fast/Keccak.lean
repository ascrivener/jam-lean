import JAM.Keccak
import JAM.Theorems.CheckedIndex.Keccak
import JAM.Fast.Blake2b

/-!
# Fast compiled Keccak-256, proved equal to `JAM.Keccak`

The faster implementation, moved out of the spec file `JAM/Keccak.lean`, with its `@[csimp]` equality.
The thin spec wrappers defined after it in the spec file are restated here (`rfl`) so that their
compiled code uses the fast form too.
-/

namespace JAM.Keccak
open JAM.Theorems.CheckedIndex

/-! ## Faster compiled form

`sponge256` turns the message into a `List UInt8`, cuts blocks out of it with `drop`/`take`, and keeps
the state in an `Array UInt64`, whose elements are boxed. The versions below keep the state in a
structure with unboxed fields (`S25`), unroll the round, and read the lanes straight from the
`ByteArray`. `sponge256_eq_sponge256Fast` proves the sponge equal to `sponge256Fast` and registers
it with `@[csimp]`; the kernel and every theorem still see `sponge256`.
-/

/-- The state $A[x + 5y]$, unboxed. -/
structure S25 where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  a6 : UInt64
  a7 : UInt64
  a8 : UInt64
  a9 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64

/-- The state as the array `round` uses. -/
def S25.toArray (s : S25) : Array UInt64 :=
  #[s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13, s.a14, s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

/-- `round` on `S25`: $\theta$, $\rho$ and $\pi$, $\chi$, $\iota$. -/
def roundS (s : S25) (r : UInt64) : S25 :=
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  let b0 := rotl (s.a0 ^^^ d0) 0
  let b1 := rotl (s.a6 ^^^ d1) 44
  let b2 := rotl (s.a12 ^^^ d2) 43
  let b3 := rotl (s.a18 ^^^ d3) 21
  let b4 := rotl (s.a24 ^^^ d4) 14
  let b5 := rotl (s.a3 ^^^ d3) 28
  let b6 := rotl (s.a9 ^^^ d4) 20
  let b7 := rotl (s.a10 ^^^ d0) 3
  let b8 := rotl (s.a16 ^^^ d1) 45
  let b9 := rotl (s.a22 ^^^ d2) 61
  let b10 := rotl (s.a1 ^^^ d1) 1
  let b11 := rotl (s.a7 ^^^ d2) 6
  let b12 := rotl (s.a13 ^^^ d3) 25
  let b13 := rotl (s.a19 ^^^ d4) 8
  let b14 := rotl (s.a20 ^^^ d0) 18
  let b15 := rotl (s.a4 ^^^ d4) 27
  let b16 := rotl (s.a5 ^^^ d0) 36
  let b17 := rotl (s.a11 ^^^ d1) 10
  let b18 := rotl (s.a17 ^^^ d2) 15
  let b19 := rotl (s.a23 ^^^ d3) 56
  let b20 := rotl (s.a2 ^^^ d2) 62
  let b21 := rotl (s.a8 ^^^ d3) 55
  let b22 := rotl (s.a14 ^^^ d4) 39
  let b23 := rotl (s.a15 ^^^ d0) 41
  let b24 := rotl (s.a21 ^^^ d1) 2
  ⟨(b0 ^^^ ((~~~ b1) &&& b2)) ^^^ r,
    b1 ^^^ ((~~~ b2) &&& b3),
    b2 ^^^ ((~~~ b3) &&& b4),
    b3 ^^^ ((~~~ b4) &&& b0),
    b4 ^^^ ((~~~ b0) &&& b1),
    b5 ^^^ ((~~~ b6) &&& b7),
    b6 ^^^ ((~~~ b7) &&& b8),
    b7 ^^^ ((~~~ b8) &&& b9),
    b8 ^^^ ((~~~ b9) &&& b5),
    b9 ^^^ ((~~~ b5) &&& b6),
    b10 ^^^ ((~~~ b11) &&& b12),
    b11 ^^^ ((~~~ b12) &&& b13),
    b12 ^^^ ((~~~ b13) &&& b14),
    b13 ^^^ ((~~~ b14) &&& b10),
    b14 ^^^ ((~~~ b10) &&& b11),
    b15 ^^^ ((~~~ b16) &&& b17),
    b16 ^^^ ((~~~ b17) &&& b18),
    b17 ^^^ ((~~~ b18) &&& b19),
    b18 ^^^ ((~~~ b19) &&& b15),
    b19 ^^^ ((~~~ b15) &&& b16),
    b20 ^^^ ((~~~ b21) &&& b22),
    b21 ^^^ ((~~~ b22) &&& b23),
    b22 ^^^ ((~~~ b23) &&& b24),
    b23 ^^^ ((~~~ b24) &&& b20),
    b24 ^^^ ((~~~ b20) &&& b21)⟩

theorem roundS_toArray (s : S25) (r : UInt64) : (roundS s r).toArray = Old.Keccak.round s.toArray r := by
  simp [roundS, Old.Keccak.round, S25.toArray, List.range_succ, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range'_succ, Id.run, Old.Keccak.rotations]
  rfl


/-- Keccak-f[1600] on `S25`. -/
def permuteS (s : S25) : S25 := Old.Keccak.rc.foldl roundS s

theorem permuteS_toArray (s : S25) : (permuteS s).toArray = Old.Keccak.permute s.toArray := by
  unfold permuteS Old.Keccak.permute
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  generalize Old.Keccak.rc.toList = l
  induction l generalizing s with
  | nil => rfl
  | cons r l ih => rw [List.foldl_cons, List.foldl_cons, ih, roundS_toArray]

/-- XOR seventeen lanes (one 136-octet block) into the state and permute. -/
def absorbS (s : S25) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : UInt64) : S25 :=
  permuteS ⟨s.a0 ^^^ w0, s.a1 ^^^ w1, s.a2 ^^^ w2, s.a3 ^^^ w3, s.a4 ^^^ w4, s.a5 ^^^ w5, s.a6 ^^^ w6, s.a7 ^^^ w7, s.a8 ^^^ w8, s.a9 ^^^ w9, s.a10 ^^^ w10, s.a11 ^^^ w11, s.a12 ^^^ w12, s.a13 ^^^ w13, s.a14 ^^^ w14, s.a15 ^^^ w15, s.a16 ^^^ w16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24⟩

/-- Lane `i` of a block, as `absorb` reads it. -/
def lane (block : List UInt8) (i : Nat) : UInt64 :=
  (List.range 8).foldr (fun k (acc : UInt64) => (acc <<< 8) ||| (block.getD (8 * i + k) 0).toUInt64) 0

/-- The lane XOR of `absorb`, before the permutation. -/
def xorLanes (a : Array UInt64) (block : List UInt8) (lanes : Nat) : Array UInt64 :=
  (List.range lanes).foldl (fun a i => a.set! i (a[i]! ^^^ lane block i)) a

theorem absorb_def (a : Array UInt64) (block : List UInt8) :
    Old.Keccak.absorb a block = Old.Keccak.permute (xorLanes a block (block.length / 8)) := rfl

theorem absorb_eq (s : S25) (block : List UInt8) (h : block.length = 136) :
    Old.Keccak.absorb s.toArray block = (absorbS s (lane block 0) (lane block 1) (lane block 2) (lane block 3) (lane block 4) (lane block 5) (lane block 6) (lane block 7) (lane block 8) (lane block 9) (lane block 10) (lane block 11) (lane block 12) (lane block 13) (lane block 14) (lane block 15) (lane block 16)).toArray := by
  rw [absorbS, permuteS_toArray, absorb_def, h]
  apply congrArg Old.Keccak.permute
  simp only [xorLanes, show 136 / 8 = 17 from rfl, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp [S25.toArray]


theorem lane_eq_wordAt (block : List UInt8) (b : ByteArray) (o : Nat)
    (hb : ∀ j, j < 136 → block.getD j 0 = Blake2b.byteAt b (o + j)) (i : Nat) (hi : i < 17) :
    lane block i = Blake2b.wordAt b (o + 8 * i) := by
  have hr : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [lane, hr, List.foldr_cons, List.foldr_nil, Blake2b.wordAt]
  have e : ∀ k, k < 8 → block.getD (8 * i + k) 0 = Blake2b.byteAt b (o + 8 * i + k) := fun k hk => by
    rw [hb _ (by omega), Nat.add_assoc]
  simp only [e 1 (by decide), e 2 (by decide), e 3 (by decide),
    e 4 (by decide), e 5 (by decide), e 6 (by decide), e 7 (by decide), Nat.add_zero]
  have e0 := e 0 (by decide); simp only [Nat.add_zero] at e0; rw [e0]

/-- `absorb` of the 136-octet block at octet `o` of `b`. -/
@[inline] def absorbAt (s : S25) (b : ByteArray) (o : Nat) : S25 :=
  absorbS s (Blake2b.wordAt b (o + 8 * 0)) (Blake2b.wordAt b (o + 8 * 1))
    (Blake2b.wordAt b (o + 8 * 2)) (Blake2b.wordAt b (o + 8 * 3)) (Blake2b.wordAt b (o + 8 * 4))
    (Blake2b.wordAt b (o + 8 * 5)) (Blake2b.wordAt b (o + 8 * 6)) (Blake2b.wordAt b (o + 8 * 7))
    (Blake2b.wordAt b (o + 8 * 8)) (Blake2b.wordAt b (o + 8 * 9)) (Blake2b.wordAt b (o + 8 * 10))
    (Blake2b.wordAt b (o + 8 * 11)) (Blake2b.wordAt b (o + 8 * 12)) (Blake2b.wordAt b (o + 8 * 13))
    (Blake2b.wordAt b (o + 8 * 14)) (Blake2b.wordAt b (o + 8 * 15)) (Blake2b.wordAt b (o + 8 * 16))

theorem absorb_block (s : S25) (b : ByteArray) (o : Nat) (block : List UInt8)
    (hl : block.length = 136) (hb : ∀ j, j < 136 → block.getD j 0 = Blake2b.byteAt b (o + j)) :
    Old.Keccak.absorb s.toArray block = (absorbAt s b o).toArray := by
  rw [absorb_eq s block hl, absorbAt]
  rw [lane_eq_wordAt block b o hb 0 (by decide), lane_eq_wordAt block b o hb 1 (by decide), lane_eq_wordAt block b o hb 2 (by decide), lane_eq_wordAt block b o hb 3 (by decide), lane_eq_wordAt block b o hb 4 (by decide), lane_eq_wordAt block b o hb 5 (by decide), lane_eq_wordAt block b o hb 6 (by decide), lane_eq_wordAt block b o hb 7 (by decide), lane_eq_wordAt block b o hb 8 (by decide), lane_eq_wordAt block b o hb 9 (by decide), lane_eq_wordAt block b o hb 10 (by decide), lane_eq_wordAt block b o hb 11 (by decide), lane_eq_wordAt block b o hb 12 (by decide), lane_eq_wordAt block b o hb 13 (by decide), lane_eq_wordAt block b o hb 14 (by decide), lane_eq_wordAt block b o hb 15 (by decide), lane_eq_wordAt block b o hb 16 (by decide)]

theorem getD_block (msg : ByteArray) (o j : Nat) (hj : j < 136) :
    ((msg.toList.drop o).take 136).getD j 0 = Blake2b.byteAt msg (o + j) := by
  rw [Blake2b.toList_eq_data_toList, List.getD_eq_getElem?_getD, List.getElem?_take,
    ite_eq_left hj, List.getElem?_drop, Array.getElem?_toList]
  unfold Blake2b.byteAt
  split
  · rename_i h
    rw [Array.getElem?_eq_getElem h, Option.getD_some]; rfl
  · rename_i h
    have h' : ¬ o + j < msg.data.size := h
    rw [Array.getElem?_eq_none (by omega), Option.getD_none]

theorem getD_toByteArray (l : List UInt8) (j : Nat) :
    l.getD j 0 = Blake2b.byteAt l.toByteArray (0 + j) := by
  rw [Nat.zero_add, List.getD_eq_getElem?_getD]
  unfold Blake2b.byteAt
  split
  · rename_i h
    rw [List.size_toByteArray] at h
    rw [List.getElem?_eq_getElem h, Option.getD_some, List.getElem_toByteArray]
  · rename_i h
    rw [List.size_toByteArray] at h
    rw [List.getElem?_eq_none (by omega), Option.getD_none]

/-- `n` full blocks of `msg`, starting with block `k`. -/
def absorbLoop (msg : ByteArray) : Nat → Nat → S25 → S25
  | 0, _, s => s
  | n + 1, k, s => absorbLoop msg n (k + 1) (absorbAt s msg (136 * k))

theorem foldl_absorbLoop (msg : ByteArray) (n k : Nat) (s : S25) (hk : 136 * (k + n) ≤ msg.size) :
    (List.range' k n).foldl (fun a k => Old.Keccak.absorb a ((msg.toList.drop (136 * k)).take 136)) s.toArray
      = (absorbLoop msg n k s).toArray := by
  induction n generalizing k s with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons, absorbLoop]
    have hl : ((msg.toList.drop (136 * k)).take 136).length = 136 := by
      simp only [List.length_take, List.length_drop, Blake2b.toList_eq_data_toList,
        Array.length_toList]
      simp only [ByteArray.size] at hk
      omega
    rw [absorb_block s msg (136 * k) _ hl (getD_block msg (136 * k)), ih (k + 1) _ (by omega)]

/-- Lane `i` of the state, as `s.toArray[i]!` reads it. -/
@[inline] def S25.get (s : S25) (i : Nat) : UInt64 :=
  match i with
  | 0 => s.a0 | 1 => s.a1 | 2 => s.a2 | 3 => s.a3
  | i => s.toArray[i]!

theorem S25.get_eq (s : S25) (i : Nat) : s.toArray[i]! = s.get i := by
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | i + 4 => rfl

/-- Append octets $k, k+1, \ldots, k+c-1$ of the state's lanes, little-endian, to `b`. -/
def squeezeLoop (s : S25) : Nat → Nat → ByteArray → ByteArray
  | 0, _, b => b
  | c + 1, k, b => squeezeLoop s c (k + 1) (b.push (s.get (k / 8) >>> (8 * (k % 8)).toUInt64).toUInt8)

theorem squeezeLoop_data (s : S25) (c k : Nat) (b : ByteArray) :
    (squeezeLoop s c k b).data.toList
      = b.data.toList ++ (List.range' k c).map fun k => (s.toArray[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8 := by
  induction c generalizing k b with
  | zero => simp [squeezeLoop]
  | succ c ih =>
    simp [squeezeLoop, ih, List.range'_succ, ByteArray.data_push, S25.get_eq]

theorem squeeze_eq (s : S25) (n : Nat) :
    squeezeLoop s n 0 (ByteArray.emptyWithCapacity n)
      = ⟨((List.range n).map fun k => (s.toArray[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8).toArray⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [squeezeLoop_data, List.range_eq_range']
  simp [ByteArray.emptyWithCapacity]; rfl

/-- The all-zero state. -/
def S25.zero : S25 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- `sponge256` on unboxed lanes, reading the full blocks straight from the message. -/
def sponge256Fast (domain : UInt8) (msg : ByteArray) : ByteArray :=
  let full := msg.size / 136
  let s := absorbLoop msg full 0 S25.zero
  let rest := (msg.extract (136 * full) msg.size).toList
  let padded := (rest ++ [domain] ++ List.replicate (136 - rest.length - 1) 0).set (136 - 1)
    ((if rest.length = 136 - 1 then domain else 0) ||| 0x80)
  squeezeLoop (absorbAt s padded.toByteArray 0) 32 0 (ByteArray.emptyWithCapacity 32)

theorem extract_toList (msg : ByteArray) (o : Nat) :
    (msg.extract o msg.size).toList = msg.toList.drop o := by
  rw [Blake2b.toList_eq_data_toList, Blake2b.toList_eq_data_toList, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop]
  apply List.take_of_length_le
  rw [List.length_drop, Array.length_toList]
  exact Nat.le_refl _

@[csimp] theorem sponge256_eq_sponge256Fast : @sponge256 = @sponge256Fast := by
  funext domain msg
  rw [← keccak_sponge256_eq_old]
  have hlen : msg.toList.length = msg.size := by
    rw [Blake2b.toList_eq_data_toList, Array.length_toList]; rfl
  have hz : Array.replicate 25 (0 : UInt64) = S25.zero.toArray := rfl
  simp only [Old.Keccak.sponge256, sponge256Fast, hlen, hz, List.range_eq_range', extract_toList]
  rw [foldl_absorbLoop msg _ 0 _ (by have := Nat.mul_div_le msg.size 136; omega)]
  have hrest : (msg.toList.drop (136 * (msg.size / 136))).length < 136 := by
    rw [List.length_drop, hlen]; have := Nat.mod_lt msg.size (show 136 > 0 by decide)
    have := Nat.div_add_mod msg.size 136; omega
  rw [absorb_block _ _ 0 _ (by simp; omega) (fun j _ => getD_toByteArray _ j), squeeze_eq,
    List.range_eq_range']

/-- `keccak256`, restated so that its compiled code uses `sponge256Fast`. -/
def keccak256Fast (msg : ByteArray) : ByteArray := sponge256 0x01 msg

@[csimp] theorem keccak256_eq_keccak256Fast : @keccak256 = @keccak256Fast := rfl

/-- `sha3_256`, restated so that its compiled code uses `sponge256Fast`. -/
def sha3_256Fast (msg : ByteArray) : ByteArray := sponge256 0x06 msg

@[csimp] theorem sha3_256_eq_sha3_256Fast : @sha3_256 = @sha3_256Fast := rfl

end JAM.Keccak
