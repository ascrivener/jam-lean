/-!
# Basic numeric definitions

Registers, sign conversions, sign extension and little-endian codecs, as defined in the
Gray Paper v0.8.0. References are to Appendix A (`sec:virtualmachine`) unless stated
otherwise; "GP (C)" refers to the serialization codec of Appendix C.

All arithmetic here is on `Nat` and `Int`, mirroring the paper's definitions over ℕ and ℤ;
`UInt64` is used only as the carrier of register values (ℕ_R = ℕ_{2^64}).
-/

namespace PVM

/-- A register value, ℕ_R ≡ ℕ_{2^64} (GP §4.7, eq. `gasregentry`). -/
abbrev RegVal := UInt64

/-- A register index, ℕ_13. -/
abbrev RegIdx := Fin 13

/-- The 13 registers ω ∈ ⟦ℕ_R⟧_13 (GP §A.1). -/
abbrev Regs := Vector UInt64 13

/-- The register index min(12, n) used by every register operand in GP §A.5. -/
def regIdx (n : Nat) : RegIdx := ⟨min 12 n, by omega⟩

/-- 2^64. -/
abbrev two64 : Nat := 2 ^ 64

/-- 2^32. -/
abbrev two32 : Nat := 2 ^ 32

namespace Num

/-- 𝒵_n, the signed interpretation of an `n`-octet natural (GP eq. `signedfunc`):
    `a` if `a < 2^(8n-1)`, otherwise `a - 2^(8n)`. -/
def signed (n : Nat) (a : Nat) : Int :=
  if a < 2 ^ (8 * n - 1) then (a : Int) else (a : Int) - 2 ^ (8 * n)

/-- 𝒵_n⁻¹, the unsigned interpretation (GP eq. `signedfunc`): `(2^(8n) + a) mod 2^(8n)`. -/
def unsigned (n : Nat) (a : Int) : Nat :=
  ((2 ^ (8 * n) + a) % (2 ^ (8 * n) : Int)).toNat

/-- 𝒳_n, sign extension of an `n`-octet natural to 64 bits (GP eq. `signedextension`):
    `x + ⌊x / 2^(8n-1)⌋ · (2^64 - 2^(8n))`.

    The paper's domain is ℕ_{2^(8n)}; we first reduce the argument modulo `2^(8n)`, which
    is the identity on that domain. For `n = 0` the only argument is `0`. -/
def sext (n : Nat) (x : Nat) : Nat :=
  let x := x % 2 ^ (8 * n)
  if n = 0 then x else x + x / 2 ^ (8 * n - 1) * (2 ^ 64 - 2 ^ (8 * n))

/-- ℰ_l, the fixed-length little-endian encoding (GP (C), "Fixed-length Integer Encoding"). -/
def encodeLE : Nat → Nat → List UInt8
  | 0, _ => []
  | l + 1, x => UInt8.ofNat (x % 256) :: encodeLE l (x / 256)

/-- ℰ_l⁻¹, little-endian decoding of an octet sequence. -/
def decodeLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLE bs

/-- Bit `i` of `x`: ⌊x / 2^i⌋ mod 2 (GP eq. `bitsfunc`). -/
def bit (x i : Nat) : Bool := x / 2 ^ i % 2 = 1

/-- The natural with bits `f 0, …, f (w-1)`: ℬ_n⁻¹ (GP eq. `bitsfunc`). -/
def ofBits (w : Nat) (f : Nat → Bool) : Nat :=
  (List.range w).foldr (fun i acc => acc + (if f i then 2 ^ i else 0)) 0

/-- Number of set bits among the low `w` bits of `x` (`count_set_bits_*`). -/
def popcount (w x : Nat) : Nat :=
  (List.range w).foldr (fun i acc => acc + (if bit x i then 1 else 0)) 0

/-- max(n ∈ ℕ_{w+1}) such that the first `n` bits of `x` (least significant first) are
    all zero (`trailing_zero_bits_*`). -/
def trailingZeros (w x : Nat) : Nat :=
  ((List.range w).find? (fun i => bit x i)).getD w

/-- max(n ∈ ℕ_{w+1}) such that the first `n` bits of the reversed bit string of `x`
    (most significant first, GP eq. `revbitsfunc`) are all zero (`leading_zero_bits_*`). -/
def leadingZeros (w x : Nat) : Nat :=
  ((List.range w).find? (fun i => bit x (w - 1 - i))).getD w

/-- Rotate the low `w` bits of `x` right by `s`: result bit `i` is bit `(i + s) mod w` of `x`. -/
def rotr (w x s : Nat) : Nat := ofBits w fun i => bit x ((i + s) % w)

/-- Rotate the low `w` bits of `x` left by `s`: result bit `(i + s) mod w` is bit `i` of `x`,
    i.e. result bit `j` is bit `(j + w - s mod w) mod w` of `x`. -/
def rotl (w x s : Nat) : Nat := ofBits w fun j => bit x ((j + w - s % w) % w)

/-- rtz, rounding towards zero (GP §A.5): division of integers rounded towards zero. -/
def divRtz (a b : Int) : Int := a.tdiv b

/-- smod (GP §A.5): `a` if `b = 0`, otherwise sgn(a)·(|a| mod |b|). -/
def smod (a b : Int) : Int :=
  if b = 0 then a else a.sign * ((a.natAbs % b.natAbs : Nat) : Int)

/-- ⌊a / 2^s⌋ for an integer `a`. -/
def floorShift (a : Int) (s : Nat) : Int := a.fdiv (2 ^ s)

end Num

/-- Reading a register. -/
@[inline] def Regs.get (ω : Regs) (r : RegIdx) : UInt64 := ω[r]

end PVM
