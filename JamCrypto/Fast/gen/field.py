#!/usr/bin/env python3
"""Generates JamCrypto/Fast/<Name>.lean: arithmetic in a prime field on fixed limbs.

Usage (from the repository root): python3 JamCrypto/Fast/gen/field.py

Elements are kept in Montgomery form a·R mod p, R = 2^(Wn), as n unsaturated limbs of W = 29 bits,
each in a UInt64, with R > 4p. Multiplication and squaring are Montgomery products by product
scanning (column by column, the reduction interleaved), fully unrolled: a column is a sum of at
most 2n products below 2^58 plus a carry, which stays below 2^64, so no product needs its own
carry. Every element is reduced (below p). The generated code is checked against `Nat`
arithmetic mod p by differential tests (`JamCryptoTest/Fast.lean`, run by cryptotest), not
proved.
"""
import sys, os

FIELDS = [
    # (module name, doc name, p)
    ("Fr", "the BLS12-381 scalar field 𝔽_r, the base field of Bandersnatch",
     0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001),
    ("Fp25519", "the base field of edwards25519, p = 2^255 − 19", 2**255 - 19),
    ("Fq", "the BLS12-381 base field 𝔽_q",
     0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab),
]

W = 29
M = (1 << W) - 1

def limbs(x, n):
    return [(x >> (W * i)) & M for i in range(n)]

class Gen:
    def __init__(self):
        self.k = 0
        self.out = []
    def fresh(self, base):
        self.k += 1
        return f"{base}{self.k}"
    def emit(self, s):
        self.out.append("  " + s)

def lit(x):
    return f"{x}"

def gen_mul(n, p, n0, square=False):
    """Montgomery product by product scanning (columns), radix 2^W, unsaturated limbs: every
    column sum stays below 2^64 (at most 2n products below 2^(2W), plus a carry)."""
    assert 2 * n * (1 << (2 * W)) + (1 << (64 - W)) < (1 << 64)
    g = Gen()
    P = limbs(p, n)
    for j in range(n):
        g.emit(f"let a{j} := a.l{j}")
    if not square:
        for j in range(n):
            g.emit(f"let b{j} := b.l{j}")
    ms = []
    r = []
    acc = None
    for k in range(2 * n - 1):
        terms = []
        if acc is not None: terms.append(acc)
        if square:
            for i in range(max(0, k - n + 1), n):
                j = k - i
                if j < i: break
                if j >= n: continue
                if i == j: terms.append(f"a{i} * a{i}")
                else: terms.append(f"2 * a{i} * a{j}")
        else:
            for i in range(max(0, k - n + 1), min(k, n - 1) + 1):
                terms.append(f"a{i} * b{k - i}")
        for i in range(max(0, k - n + 1), min(k, n)):
            if i < len(ms) and 0 <= k - i < n and P[k - i] != 0:
                terms.append(f"{ms[i]} * {P[k - i]}")
        s = g.fresh("s")
        g.emit(f"let {s} := " + (tree(terms) if terms else "0"))
        if k < n:
            m = g.fresh("m")
            g.emit(f"let {m} := ({s} * {n0}) &&& {M}")
            ms.append(m)
            s2 = g.fresh("s")
            g.emit(f"let {s2} := {s} + {m} * {P[0]}")
            a2 = g.fresh("c"); g.emit(f"let {a2} := {s2} >>> {W}")
            acc = a2
        else:
            rk = g.fresh("r"); g.emit(f"let {rk} := {s} &&& {M}")
            r.append(rk)
            a2 = g.fresh("c"); g.emit(f"let {a2} := {s} >>> {W}")
            acc = a2
    r.append(acc)
    final_sub(g, n, P, r, None)
    return g.out

def final_sub(g, n, P, t, top):
    """Emit: if (top·2^(Wn) + t) ≥ p then t − p else t."""
    bw = None
    d = []
    for j in range(n):
        x = g.fresh("x")
        e = f"{t[j]} - {P[j]}"
        if bw is not None: e += f" - {bw}"
        g.emit(f"let {x} := {e}")
        dj = g.fresh("d"); g.emit(f"let {dj} := {x} &&& {M}")
        b2 = g.fresh("w"); g.emit(f"let {b2} := {x} >>> 63")
        d.append(dj); bw = b2
    cond = f"{bw} == 0" if top is None else f"{top} != 0 || {bw} == 0"
    g.emit(f"if {cond} then ⟨{', '.join(d)}⟩ else ⟨{', '.join(t)}⟩")

def gen_add(n, p):
    g = Gen()
    P = limbs(p, n)
    c = None
    t = []
    for j in range(n):
        s = g.fresh("s")
        e = f"a.l{j} + b.l{j}" + (f" + {c}" if c else "")
        g.emit(f"let {s} := {e}")
        tj = g.fresh("t"); g.emit(f"let {tj} := {s} &&& {M}")
        c2 = g.fresh("c"); g.emit(f"let {c2} := {s} >>> {W}")
        t.append(tj); c = c2
    final_sub(g, n, P, t, c)
    return g.out

def gen_sub(n, p):
    g = Gen()
    P = limbs(p, n)
    bw = None
    d = []
    for j in range(n):
        x = g.fresh("x")
        e = f"a.l{j} - b.l{j}" + (f" - {bw}" if bw else "")
        g.emit(f"let {x} := {e}")
        dj = g.fresh("d"); g.emit(f"let {dj} := {x} &&& {M}")
        b2 = g.fresh("w"); g.emit(f"let {b2} := {x} >>> 63")
        d.append(dj); bw = b2
    # if borrow, add p
    c = None
    e2 = []
    for j in range(n):
        s = g.fresh("s")
        e = f"{d[j]} + {P[j]}" + (f" + {c}" if c else "")
        g.emit(f"let {s} := {e}")
        tj = g.fresh("t"); g.emit(f"let {tj} := {s} &&& {M}")
        c2 = g.fresh("c"); g.emit(f"let {c2} := {s} >>> {W}")
        e2.append(tj); c = c2
    g.emit(f"if {bw} == 0 then ⟨{', '.join(d)}⟩ else ⟨{', '.join(e2)}⟩")
    return g.out

def tree(terms):
    """A sum as a balanced tree, so that the C compiler sees independent additions."""
    if len(terms) == 1:
        return terms[0]
    h = len(terms) // 2
    return f"({tree(terms[:h])} + {tree(terms[h:])})"

def ctor(xs):
    return "⟨" + ", ".join(str(x) for x in xs) + "⟩"

def bits_msb(e):
    return [c == "1" for c in bin(e)[2:]]

def gen_module(name, doc, p):
    n = (p.bit_length() + 2 + W - 1) // W
    R = 1 << (W * n)
    n0 = (-pow(p, -1, 1 << W)) % (1 << W)
    r2 = R * R % p
    one = R % p
    L = []
    w = L.append
    w("/-! This file is generated by `JamCrypto/Fast/gen/field.py`; do not edit it by hand. -/")
    w("")
    w("/-!")
    w(f"# {name}: {doc}, on {n} limbs of {W} bits")
    w("")
    w("An element is the Montgomery form a·R mod p (R = 2^" + str(W * n) + ") of its value a, as " + str(n))
    w(str(W) + "-bit limbs (least significant first), each held in a `UInt64`. Every element is reduced.")
    w("`ofNat`/`toNat` convert from and to the value. The arithmetic computes the same function as")
    w("`Nat` arithmetic mod p (`(ofNat a * ofNat b).toNat = a * b % p`, and so on); this is checked by")
    w("differential tests (`JamCryptoTest/Fast.lean`), not proved.")
    w("-/")
    w("")
    w(f"namespace JamCrypto.Fast.{name}")
    w("")
    w("set_option linter.unusedVariables false")
    w("set_option maxRecDepth 100000")
    w("")
    w("/-- The modulus. -/")
    w(f"def p : Nat := {hex(p)}")
    w("")
    w("/-- An element of the field, in Montgomery form. -/")
    w("structure Elem where")
    for j in range(n):
        w(f"  l{j} : UInt64")
    w("")
    w("instance : Inhabited Elem := ⟨" + ctor([0] * n) + "⟩")
    w("")
    w("/-- 0. -/")
    w("def zero : Elem := " + ctor([0] * n))
    w("/-- 1 (R mod p). -/")
    w("def one : Elem := " + ctor(limbs(one, n)))
    w("/-- R² mod p, the Montgomery form of R. -/")
    w("def r2 : Elem := " + ctor(limbs(r2, n)))
    w("")
    w("/-- The Montgomery product a·b·R⁻¹ mod p. -/")
    w("def mul (a b : Elem) : Elem :=")
    L.extend(gen_mul(n, p, n0))
    w("")
    w("/-- a + b. -/")
    w("def add (a b : Elem) : Elem :=")
    L.extend(gen_add(n, p))
    w("")
    w("/-- a − b. -/")
    w("def sub (a b : Elem) : Elem :=")
    L.extend(gen_sub(n, p))
    w("")
    w("/-- −a. -/")
    w("@[inline] def neg (a : Elem) : Elem := sub zero a")
    w("/-- a² (a Montgomery square). -/")
    w("def sq (a : Elem) : Elem :=")
    L.extend(gen_mul(n, p, n0, square=True))
    w("/-- 2a. -/")
    w("@[inline] def dbl (a : Elem) : Elem := add a a")
    w("")
    w("/-- Equality (elements are reduced, so limbwise). -/")
    w("def beq (a b : Elem) : Bool :=")
    w("  " + " && ".join(f"a.l{j} == b.l{j}" for j in range(n)))
    w("")
    w("instance : BEq Elem := ⟨beq⟩")
    w("instance : Add Elem := ⟨add⟩")
    w("instance : Sub Elem := ⟨sub⟩")
    w("instance : Mul Elem := ⟨mul⟩")
    w("instance : Neg Elem := ⟨neg⟩")
    w("")
    w("/-- a = 0. -/")
    w("def isZero (a : Elem) : Bool :=")
    w("  " + " && ".join(f"a.l{j} == 0" for j in range(n)))
    w("")
    w("/-- The limbs of x mod 2^" + str(W * n) + ", unreduced (not in Montgomery form). -/")
    w("def rawOfNat (x : Nat) : Elem :=")
    w("  " + ctor([f"UInt64.ofNat (x >>> {W * j} % {1 << W})" for j in range(n)]))
    w("")
    w("/-- The number the limbs stand for, read as plain limbs. -/")
    w("def rawToNat (a : Elem) : Nat :=")
    w("  " + " + ".join(f"(a.l{j}.toNat <<< {W * j})" for j in range(n)))
    w("")
    w("/-- The element with value x mod p. -/")
    w("def ofNat (x : Nat) : Elem := mul (rawOfNat (x % p)) r2")
    w("")
    w("/-- The value (below p) of an element. -/")
    w("def toNat (a : Elem) : Nat := rawToNat (mul a " + ctor([1] + [0] * (n - 1)) + ")")
    w("")
    w("/-- The value of an element is odd. -/")
    w("def isOdd (a : Elem) : Bool := (mul a " + ctor([1] + [0] * (n - 1)) + ").l0 &&& 1 == 1")
    w("")
    w("/-- The bits of e, most significant first (empty for 0). -/")
    w("def bitsMsb (e : Nat) : Array Bool := Id.run do")
    w("  let n := if e == 0 then 0 else e.log2 + 1")
    w("  let mut out : Array Bool := Array.mkEmpty n")
    w("  for i in [0:n] do")
    w("    out := out.push (e.testBit (n - 1 - i))")
    w("  return out")
    w("")
    w("/-- a^e for e given by its bits, most significant first. -/")
    w("def powBits (a : Elem) (bits : Array Bool) : Elem := Id.run do")
    w("  let mut r := one")
    w("  for b in bits do")
    w("    r := sq r")
    w("    if b then r := mul r a")
    w("  return r")
    w("")
    w("/-- a^e. -/")
    w("def pow (a : Elem) (e : Nat) : Elem := powBits a (bitsMsb e)")
    w("")
    w("/-- The bits of p − 2. -/")
    w("def pMinus2Bits : Array Bool := bitsMsb (p - 2)")
    w("")
    w("/-- a⁻¹ (Fermat: a^(p−2)); 0 for 0. -/")
    w("def inv (a : Elem) : Elem := powBits a pMinus2Bits")
    w("")
    w("/-- The bits of (p − 1)/2. -/")
    w("def halfBits : Array Bool := bitsMsb ((p - 1) / 2)")
    w("")
    w("/-- a is a nonzero square (Euler's criterion). -/")
    w("def isSquare (a : Elem) : Bool := powBits a halfBits == one")
    w("")
    w("/-- Batch inversion (Montgomery's trick); zero entries map to zero. -/")
    w("def batchInv (xs : Array Elem) : Array Elem := Id.run do")
    w("  let n := xs.size")
    w("  let mut pre : Array Elem := Array.mkEmpty n")
    w("  let mut acc := one")
    w("  for x in xs do")
    w("    pre := pre.push acc")
    w("    if !isZero x then acc := mul acc x")
    w("  let mut iv := inv acc")
    w("  let mut out : Array Elem := Array.replicate n zero")
    w("  for k in [0:n] do")
    w("    let i := n - 1 - k")
    w("    let x := xs[i]!")
    w("    if !isZero x then")
    w("      out := out.set! i (mul iv pre[i]!)")
    w("      iv := mul iv x")
    w("  return out")
    w("")
    w("@[inline] def Elem.toNat (a : Elem) : Nat := JamCrypto.Fast." + name + ".toNat a")
    w("@[inline] def Elem.isZero (a : Elem) : Bool := JamCrypto.Fast." + name + ".isZero a")
    w("@[inline] def Elem.inv (a : Elem) : Elem := JamCrypto.Fast." + name + ".inv a")
    w("@[inline] def Elem.sq (a : Elem) : Elem := JamCrypto.Fast." + name + ".sq a")
    w("")
    w(f"end JamCrypto.Fast.{name}")
    return "\n".join(L) + "\n"

def main():
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    for name, doc, p in FIELDS:
        with open(os.path.join(root, f"{name}.lean"), "w") as f:
            f.write(gen_module(name, doc, p))

main()
