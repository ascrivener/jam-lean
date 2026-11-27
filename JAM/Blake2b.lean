/-!
# Blake2b (RFC 7693), as used by the Gray Paper's ℋ (GP v0.8.1 §3.8: ℋ is Blake2b-256)

Unkeyed Blake2b with a configurable digest length, in pure Lean: total, no `extern` code, so it
can be evaluated by the kernel.
-/

namespace JAM.Blake2b


/-- The initialization vector (RFC 7693 §2.6). -/
def iv : Vector UInt64 8 := #v[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The message schedule σ (RFC 7693 §2.7); rounds 10 and 11 reuse rows 0 and 1. Each row is a
    permutation of the sixteen message-word indices. -/
def sigma : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #v[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #v[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #v[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #v[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #v[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #v[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #v[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #v[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #v[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- Rotate right. -/
@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- The mixing function G (RFC 7693 §3.1) on the working vector v₀ … v₁₅. -/
def mix (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) : Vector UInt64 16 := Id.run do
  let mut v := v
  v := v.set a (v[a] + v[b] + x)
  v := v.set d (rotr (v[d] ^^^ v[a]) 32)
  v := v.set c (v[c] + v[d])
  v := v.set b (rotr (v[b] ^^^ v[c]) 24)
  v := v.set a (v[a] + v[b] + y)
  v := v.set d (rotr (v[d] ^^^ v[a]) 16)
  v := v.set c (v[c] + v[d])
  v := v.set b (rotr (v[b] ^^^ v[c]) 63)
  return v

/-- A 128-octet block as sixteen little-endian 64-bit words. -/
def words (block : List UInt8) : Vector UInt64 16 :=
  Vector.ofFn fun i =>
    (List.range 8).foldr (fun k acc => (acc <<< 8) ||| (block.getD (8 * i + k) 0).toUInt64) 0

/-- The compression function F (RFC 7693 §3.2), with byte counter `t` and final-block flag `last`. -/
def compress (h : Vector UInt64 8) (block : List UInt8) (t : Nat) (last : Bool) : Vector UInt64 8 := Id.run do
  let m := words block
  let mut v := h ++ iv
  v := v.set 12 (v[12] ^^^ UInt64.ofNat (t % 2 ^ 64))
  v := v.set 13 (v[13] ^^^ UInt64.ofNat (t / 2 ^ 64))
  if last then v := v.set 14 (v[14] ^^^ 0xFFFFFFFFFFFFFFFF)
  for r in [0:12] do
    let s := sigma[r % 10]'(Nat.mod_lt _ (by decide))
    v := mix v 0 4 8 12 m[s[0]] m[s[1]]
    v := mix v 1 5 9 13 m[s[2]] m[s[3]]
    v := mix v 2 6 10 14 m[s[4]] m[s[5]]
    v := mix v 3 7 11 15 m[s[6]] m[s[7]]
    v := mix v 0 5 10 15 m[s[8]] m[s[9]]
    v := mix v 1 6 11 12 m[s[10]] m[s[11]]
    v := mix v 2 7 8 13 m[s[12]] m[s[13]]
    v := mix v 3 4 9 14 m[s[14]] m[s[15]]
  return Vector.ofFn fun i => h[i] ^^^ v[i.val] ^^^ v[i.val + 8]

/-- Process the message's 128-octet blocks, the last one (possibly empty, for an empty message)
    with the final-block flag. The byte counter is the number of octets consumed so far. -/
def blocks (h : Vector UInt64 8) (msg : ByteArray) : Vector UInt64 8 :=
  let len := msg.size
  let nb := max 1 ((len + 127) / 128)
  let block (k : Nat) : List UInt8 := (msg.extract (128 * k) (128 * k + 128)).toList
  let h := (List.range (nb - 1)).foldl (fun h k => compress h (block k) (128 * (k + 1)) false) h
  compress h (block (nb - 1)) len true

/-- Blake2b with an `n`-octet digest (1 ≤ n ≤ 64), unkeyed (RFC 7693 §3.3). The digest octets are
    read from the eight-word state with `getD`, whose default is never used for n ≤ 64
    (`hash_getD_unused`). -/
def hash (n : Nat) (msg : ByteArray) : ByteArray :=
  let h := iv.set 0 (iv[0] ^^^ 0x01010000 ^^^ UInt64.ofNat n)
  let h := blocks h msg
  let out := (List.range n).map fun k => ((h[k / 8]?.getD 0) >>> (8 * (k % 8)).toUInt64).toUInt8
  ⟨out.toArray⟩

theorem hash_getD_unused (n k : Nat) (hn : n ≤ 64) (hk : k < n) : k / 8 < 8 := by omega

/-- ℋ: Blake2b-256 (GP §3.8). -/
def hash256 (msg : ByteArray) : ByteArray := hash 32 msg

end JAM.Blake2b
