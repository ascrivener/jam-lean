#!/usr/bin/env python3
"""Generates JamCrypto/Fast/<Name>.lean: arithmetic in a prime field on fixed limbs, with proofs.

Usage (from the repository root): python3 JamCrypto/Fast/gen/field.py

Elements are kept in Montgomery form a·R mod p, R = 2^(Wn), as n unsaturated limbs of W = 29 bits,
each in a UInt64, with R > 4p. Multiplication and squaring are Montgomery products by product
scanning (column by column, the reduction interleaved), fully unrolled: a column is a sum of at
most 2n products below 2^58 plus a carry, which stays below 2^64, so no product needs its own
carry. Every element is reduced (below p).

Each operation comes with a generated proof that it computes the `Nat` function mod p it stands
for (`mul_spec`, `sq_spec`, `add_spec`, `sub_spec`): the proof states the value of every
intermediate `let` as a `Nat` expression (each checked by `omega` from the previous ones and the
generic lemmas of `JamCrypto/Fast/Limbs.lean`), then concludes with `omega` (and `grind` for the
expansion of the product of two limb sums).
"""
import os

FIELDS = [
    ("Fr", "the BLS12-381 scalar field 𝔽_r, the base field of Bandersnatch",
     0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001),
    ("Fp25519", "the base field of edwards25519, p = 2^255 − 19", 2**255 - 19),
    ("Fq", "the BLS12-381 base field 𝔽_q",
     0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab),
]

W = 29
M = (1 << W) - 1
SIMP = "UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub, UInt64.reduceToNat, land_mask, shr29, shr63"

def limbs(x, n):
    return [(x >> (W * i)) & M for i in range(n)]

def tree(terms):
    if len(terms) == 1:
        return terms[0]
    h = len(terms) // 2
    return f"({tree(terms[:h])} + {tree(terms[h:])})"

class Gen:
    """Straight-line code: each binding has a name, UInt64 code and its Nat value (as Lean text)."""
    def __init__(self):
        self.k = 0
        self.binds = []  # (name, code, natRHS)
        self.groups = []  # (index into binds after which to emit, [clean facts])
        self.dropped = []  # clean equalities, cleared before the final omega
        self.summary = []  # facts proved from all clean facts, before the final omega
    def clean(self, *facts):
        """Linear facts implied by the bindings so far; the raw facts are cleared after them."""
        self.groups.append((len(self.binds), list(facts)))
    def bind(self, base, code, nat):
        self.k += 1
        name = f"{base}{self.k}"
        self.binds.append((name, code, nat))
        return name

def lsum(names):
    return " + ".join(f"{N(x)} * 2^{W * j}" for j, x in enumerate(names))

def N(v):
    """Nat value of an operand (a let name or a limb projection)."""
    return f"{v}.toNat"

def column_code(g, k, n, P, ms, acc, square):
    terms = []
    if acc is not None:
        terms.append((acc, N(acc)))
    if square:
        for i in range(max(0, k - n + 1), n):
            j = k - i
            if j < i: break
            if j >= n: continue
            if i == j:
                terms.append((f"a.l{i} * a.l{i}", f"a.l{i}.toNat * a.l{i}.toNat"))
            else:
                terms.append((f"a.l{i} * a.l{j} * 2", f"a.l{i}.toNat * a.l{j}.toNat * 2"))
    else:
        for i in range(max(0, k - n + 1), min(k, n - 1) + 1):
            terms.append((f"a.l{i} * b.l{k - i}", f"a.l{i}.toNat * b.l{k - i}.toNat"))
    for i in range(max(0, k - n + 1), min(k, n)):
        if i < len(ms) and 0 <= k - i < n and P[k - i] != 0:
            terms.append((f"{ms[i]} * {P[k - i]}", f"{N(ms[i])} * {P[k - i]}"))
    code = tree([c for c, _ in terms]) if terms else "0"
    nat = " + ".join(f"({x})" for _, x in terms) if terms else "0"
    return code, nat

def final_sub(g, n, P, t, top):
    """if top·2^(Wn) + Σ t ≥ p then t − p else t. t: operand names. Returns the result text."""
    bw = None
    d = []
    for j in range(n):
        code = f"{t[j]} - {P[j]}" + (f" - {bw}" if bw else "")
        nat = f"({N(t[j])} + 2^65 - {P[j]}" + (f" - {N(bw)}" if bw else "") + ") % 2^64"
        x = g.bind("x", code, nat)
        dj = g.bind("d", f"{x} &&& {M}", f"{N(x)} % 2^{W}")
        w = g.bind("w", f"{x} >>> 63", f"{N(x)} / 2^63")
        g.clean(f"{N(dj)} + {P[j]}" + (f" + {N(bw)}" if bw else "") + f" = {N(t[j])} + 2^{W} * {N(w)}",
                (f"{N(dj)} < 2^{W}", True), (f"{N(w)} ≤ 1", j == n - 1))
        d.append(dj); bw = w
    cond = f"{bw} == 0" if top is None else f"{top} != 0 || {bw} == 0"
    g.summary.append(f"{lsum(d)} + {sum(P[j] << (W * j) for j in range(n))} = {lsum(t)} + 2^{W * n} * {N(bw)}")
    return cond, d, t

def gen_mul(n, p, n0, square):
    g = Gen()
    P = limbs(p, n)
    ms, r, acc = [], [], None
    for k in range(2 * n - 1):
        code, nat = column_code(g, k, n, P, ms, acc, square)
        s = g.bind("s", code, nat)
        if k < n:
            m = g.bind("m", f"({s} * {n0}) &&& {M}", f"({N(s)} * {n0}) % 2^{W}")
            ms.append(m)
            s2 = g.bind("s", f"{s} + {m} * {P[0]}", f"{N(s)} + {N(m)} * {P[0]}")
            acc = g.bind("c", f"{s2} >>> {W}", f"{N(s2)} / 2^{W}")
            g.clean(f"{nat} + {N(m)} * {P[0]} = 2^{W} * {N(acc)}", (f"{N(m)} < 2^{W}", True), f"{N(acc)} < 2^37")
        else:
            rk = g.bind("r", f"{s} &&& {M}", f"{N(s)} % 2^{W}")
            r.append(rk)
            acc = g.bind("c", f"{s} >>> {W}", f"{N(s)} / 2^{W}")
            g.clean(f"{nat} = {N(rk)} + 2^{W} * {N(acc)}", (f"{N(rk)} < 2^{W}", True), (f"{N(acc)} < 2^37", k == 2 * n - 2))
    r.append(acc)
    if square:
        expn = " + ".join((f"a.l{i}.toNat * a.l{i}.toNat * 2^{2 * W * i}" if i == j else
                          f"a.l{i}.toNat * a.l{j}.toNat * 2 * 2^{W * (i + j)}")
                         for i in range(n) for j in range(i, n))
    else:
        expn = " + ".join(f"a.l{i}.toNat * b.l{j}.toNat * 2^{W * (i + j)}" for i in range(n) for j in range(n))
    g.summary.append(f"({lsum(r)}) * 2^{W * n} = {expn} + ({lsum(ms)}) * {p}")
    g.expansion = expn
    cond, d, t = final_sub(g, n, P, r, None)
    return g, cond, d, t, ms

def gen_add(n, p):
    g = Gen()
    P = limbs(p, n)
    c, t = None, []
    for j in range(n):
        code = f"a.l{j} + b.l{j}" + (f" + {c}" if c else "")
        nat = f"a.l{j}.toNat + b.l{j}.toNat" + (f" + {N(c)}" if c else "")
        s = g.bind("s", code, nat)
        tj = g.bind("t", f"{s} &&& {M}", f"{N(s)} % 2^{W}")
        t.append(tj)
        c = g.bind("c", f"{s} >>> {W}", f"{N(s)} / 2^{W}")
        g.clean(f"{nat} = {N(tj)} + 2^{W} * {N(c)}", (f"{N(tj)} < 2^{W}", True), (f"{N(c)} ≤ 1", j == n - 1))
    g.summary.append(f"{lsum(t)} + 2^{W * n} * {N(c)} = {val_expr('a', n)} + {val_expr('b', n)}")
    cond, d, tt = final_sub(g, n, P, t, c)
    return g, cond, d, tt

def gen_sub(n, p):
    g = Gen()
    P = limbs(p, n)
    bw, d = None, []
    for j in range(n):
        code = f"a.l{j} - b.l{j}" + (f" - {bw}" if bw else "")
        nat = f"(a.l{j}.toNat + 2^65 - b.l{j}.toNat" + (f" - {N(bw)}" if bw else "") + ") % 2^64"
        x = g.bind("x", code, nat)
        dj = g.bind("d", f"{x} &&& {M}", f"{N(x)} % 2^{W}")
        d.append(dj)
        w = g.bind("w", f"{x} >>> 63", f"{N(x)} / 2^63")
        g.clean(f"{N(dj)} + b.l{j}.toNat" + (f" + {N(bw)}" if bw else "") + f" = a.l{j}.toNat + 2^{W} * {N(w)}",
                (f"{N(dj)} < 2^{W}", True), (f"{N(w)} ≤ 1", j == n - 1))
        bw = w
    c, e = None, []
    for j in range(n):
        code = f"{d[j]} + {P[j]}" + (f" + {c}" if c else "")
        nat = f"{N(d[j])} + {P[j]}" + (f" + {N(c)}" if c else "")
        s = g.bind("s", code, nat)
        tj = g.bind("t", f"{s} &&& {M}", f"{N(s)} % 2^{W}")
        e.append(tj)
        c = g.bind("c", f"{s} >>> {W}", f"{N(s)} / 2^{W}")
        g.clean(f"{nat} = {N(tj)} + 2^{W} * {N(c)}", (f"{N(tj)} < 2^{W}", True), (f"{N(c)} ≤ 1", j == n - 1))
    g.summary.append(f"{lsum(d)} + {val_expr('b', n)} = {val_expr('a', n)} + 2^{W * n} * {N(bw)}")
    g.summary.append(f"{lsum(e)} + 2^{W * n} * {N(c)} = {lsum(d)} + {p}")
    return g, f"{bw} == 0", d, e

def emit_code(L, g, cond, d, t):
    for name, code, _ in g.binds:
        L.append(f"  let {name} := {code}")
    L.append(f"  if {cond} then ⟨{', '.join(d)}⟩ else ⟨{', '.join(t)}⟩")

def emit_facts(L, g, ind="  "):
    """One `have` per binding (its Nat value, below 2^64); after each group, its clean linear facts,
    then the raw facts of the group are cleared (so no `omega` call sees their truncated
    subtractions and remainders)."""
    gi = 0
    pending = []
    cnt = 0
    for idx, (name, code, nat) in enumerate(g.binds):
        L.append(f"{ind}have h_{name} : {name}.toNat = {nat} := by simp only [{name}, {SIMP}] <;> omega")
        L.append(f"{ind}have l_{name} := UInt64.toNat_lt {name}")
        pending += [f"h_{name}", f"l_{name}"]
        while gi < len(g.groups) and g.groups[gi][0] == idx + 1:
            for fact in g.groups[gi][1]:
                cnt += 1
                text, keep = fact if isinstance(fact, tuple) else (fact, False)
                L.append(f"{ind}have k{cnt} : {text} := by omega")
                if not keep:
                    g.dropped.append(f"k{cnt}")
            L.append(f"{ind}clear {' '.join(pending)}")
            pending = []
            gi += 1
    for i, fact in enumerate(g.summary):
        L.append(f"{ind}have sum{i} : {fact} := by omega")
    L.append(f"{ind}clear {' '.join(g.dropped)}")
def val_expr(prefix, n):
    return " + ".join(f"{prefix}.l{j}.toNat * 2^{W * j}" for j in range(n))

def ok_unpack(L, v, n, ind="  "):
    L.append(f"{ind}obtain ⟨{', '.join(f'h{v}{j}' for j in range(n))}, h{v}v⟩ := h{v}")
    L.append(f"{ind}simp only [Elem.val, p] at h{v}v")

def emit_cond_split(L, cond_kind, n, ind="  "):
    L.append(f"{ind}split")
    for branch in ["next hc =>", "next hc =>"]:
        L.append(f"{ind}· {'' if True else ''}")
    return

def finish(L, cond_top, ind="  "):
    """Split on the final comparison and close both branches with omega."""
    L.append(f"{ind}split <;> rename_i hc <;>")
    L.append(f"{ind}  simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq, ← UInt64.toNat_inj, UInt64.reduceToNat, Bool.not_eq_true'] at hc <;>")
    L.append(f"{ind}  simp only [Elem.Ok, Elem.val, p] <;> omega")

def gen_module(name, doc, p):
    n = (p.bit_length() + 2 + W - 1) // W
    R = 1 << (W * n)
    n0 = (-pow(p, -1, 1 << W)) % (1 << W)
    r2 = R * R % p
    one = R % p
    rinv = pow(R, -1, p)
    P = limbs(p, n)
    L = []
    w = L.append
    w("import JamCrypto.Fast.Limbs")
    w("")
    w("/-! This file is generated by `JamCrypto/Fast/gen/field.py`; do not edit it by hand. -/")
    w("")
    w("/-!")
    w(f"# {name}: {doc}, on {n} limbs of {W} bits")
    w("")
    w(f"An element is the Montgomery form a·R mod p (R = 2^{W * n}) of its value a, as {n} {W}-bit limbs")
    w("(least significant first), each held in a `UInt64`. Every element is reduced: `Elem.Ok` (limbs")
    w("below 2^29, the number they stand for, `Elem.val`, below p). The value of an element is")
    w("`Elem.value` = val·R⁻¹ mod p.")
    w("")
    w("Proved here: `mul_spec`, `sq_spec`, `add_spec`, `sub_spec` (each operation keeps `Ok` and computes")
    w("the corresponding `Nat` operation mod p on values), and on top of them the value-level")
    w("statements in `JamCrypto/Fast/FieldProps` style below (`value_mul`, …, `toNat_ofNat`).")
    w("-/")
    w("")
    w(f"namespace JamCrypto.Fast.{name}")
    w("")
    w("set_option linter.unusedVariables false")
    w("set_option linter.unusedSimpArgs false")
    w("set_option maxRecDepth 100000")
    w("set_option maxHeartbeats 0")
    w("set_option exponentiation.threshold 2000")
    w("")
    w("/-- The modulus. -/")
    w(f"def p : Nat := {hex(p)}")
    w("")
    w(f"/-- R = 2^{W * n}. -/")
    w(f"def R : Nat := 2 ^ {W * n}")
    w("")
    w("/-- R⁻¹ mod p. -/")
    w(f"def rInv : Nat := {rinv}")
    w("")
    w("theorem R_rInv : R * rInv % p = 1 := by rfl")
    w("")
    w("/-- An element of the field, in Montgomery form. -/")
    w("structure Elem where")
    for j in range(n):
        w(f"  l{j} : UInt64")
    w("")
    w("/-- The number the limbs stand for. -/")
    w("def Elem.val (a : Elem) : Nat :=")
    w("  " + val_expr("a", n))
    w("")
    w("/-- Reduced: limbs below 2^29, value below p. -/")
    w("def Elem.Ok (a : Elem) : Prop :=")
    w("  " + " ∧ ".join(f"a.l{j}.toNat < 2^{W}" for j in range(n)) + " ∧ a.val < p")
    w("")
    w("/-- The field element an element stands for: val·R⁻¹ mod p. -/")
    w("def Elem.value (a : Elem) : Nat := a.val * rInv % p")
    w("")
    w("instance : Inhabited Elem := ⟨⟨" + ", ".join(["0"] * n) + "⟩⟩")
    w("")
    w("/-- 0. -/")
    w("def zero : Elem := ⟨" + ", ".join(["0"] * n) + "⟩")
    w("/-- 1 (R mod p). -/")
    w("def one : Elem := ⟨" + ", ".join(map(str, limbs(one, n))) + "⟩")
    w("/-- R² mod p, the Montgomery form of R. -/")
    w("def r2 : Elem := ⟨" + ", ".join(map(str, limbs(r2, n))) + "⟩")
    w("/-- The plain number 1 (the Montgomery form of R⁻¹). -/")
    w("def raw1 : Elem := ⟨" + ", ".join(["1"] + ["0"] * (n - 1)) + "⟩")
    w("")
    for (fname, sq, docl) in [("mul", False, "The Montgomery product a·b·R⁻¹ mod p."), ("sq", True, "The Montgomery square a²·R⁻¹ mod p.")]:
        g, cond, d, t, ms = gen_mul(n, p, n0, sq)
        w(f"/-- {docl} -/")
        w(f"def {fname} (a{'' if sq else ' b'} : Elem) : Elem :=")
        emit_code(L, g, cond, d, t)
        w("")
        bs = "a" if sq else "b"
        # expansion of the product
        w(f"theorem {fname}_expand (a{'' if sq else ' b'} : Elem) : a.val * {bs}.val =")
        w("    " + g.expansion + " := by")
        w("  simp only [Elem.val]; grind")
        w("")
        w(f"theorem {fname}_spec (a{'' if sq else ' b'} : Elem) (ha : a.Ok){'' if sq else ' (hb : b.Ok)'} :")
        w(f"    ({fname} a{'' if sq else ' b'}).Ok ∧ ({fname} a{'' if sq else ' b'}).val * R % p = a.val * {bs}.val % p := by")
        w(f"  obtain ⟨{', '.join(f'ha{j}' for j in range(n))}, hav⟩ := ha")
        if not sq:
            w(f"  obtain ⟨{', '.join(f'hb{j}' for j in range(n))}, hbv⟩ := hb")
        w(f"  have hABlt := Nat.mul_lt_mul'' hav {'hav' if sq else 'hbv'}")
        w(f"  rw [{fname}_expand] at hABlt ⊢")
        w(f"  simp only [Elem.val, p] at hav{'' if sq else ' hbv'} hABlt")
        for i in range(n):
            for j in range(n):
                if sq and j < i: continue
                w(f"  have hp{i}_{j} := mul_lt29 ha{i} h{bs}{j}")
        w(f"  simp only [R, p]")
        w(f"  unfold {fname}")
        w("  extract_lets " + " ".join(nm for nm, _, _ in g.binds))
        emit_facts(L, g)
        finish(L, None)
        w("")
    g, cond, d, t = gen_add(n, p)
    w("/-- a + b. -/")
    w("def add (a b : Elem) : Elem :=")
    emit_code(L, g, cond, d, t)
    w("")
    w("theorem add_spec (a b : Elem) (ha : a.Ok) (hb : b.Ok) :")
    w("    (add a b).Ok ∧ (add a b).val = (a.val + b.val) % p := by")
    ok_unpack(L, "a", n); ok_unpack(L, "b", n)
    w("  simp only [Elem.val, p]")
    w("  unfold add")
    w("  extract_lets " + " ".join(nm for nm, _, _ in g.binds))
    emit_facts(L, g)
    finish(L, True)
    w("")
    g, cond, d, t = gen_sub(n, p)
    w("/-- a − b. -/")
    w("def sub (a b : Elem) : Elem :=")
    emit_code(L, g, cond, d, t)
    w("")
    w("theorem sub_spec (a b : Elem) (ha : a.Ok) (hb : b.Ok) :")
    w("    (sub a b).Ok ∧ (sub a b).val = (a.val + p - b.val) % p := by")
    ok_unpack(L, "a", n); ok_unpack(L, "b", n)
    w("  simp only [Elem.val, p]")
    w("  unfold sub")
    w("  extract_lets " + " ".join(nm for nm, _, _ in g.binds))
    emit_facts(L, g)
    finish(L, None)
    w("")
    w(f"end JamCrypto.Fast.{name}")
    return "\n".join(L) + "\n"

def main():
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    import sys
    only = sys.argv[1:] or [f[0] for f in FIELDS]
    for name, doc, p in FIELDS:
        if name in only:
            with open(os.path.join(root, f"{name}.lean"), "w") as f:
                f.write(gen_module(name, doc, p))

main()
