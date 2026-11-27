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
        self.kept = []  # (name, text) of the bounds kept to the end
        self.skip = set()
        self.factname = {}  # bindings whose facts come from a group's lemma instead
    def clean(self, *facts, chain=None, proof=None):
        """Linear facts implied by the bindings so far; the raw facts are cleared after them. With
        `chain`, the first fact is an equation u + c = t + 2^W·c' that extends that carry chain.
        With `proof`, the facts are obtained at once from that term (a generic lemma)."""
        self.groups.append((len(self.binds), list(facts), chain, proof))
    def bnd(self, v, one):
        return f"@B[{N(v)} ≤ 1]"
    def eqn(self, chain, u, cprev, t, cnext, *bounds, proof=None):
        self.clean(f"{u} + {cprev} = {t} + 2^{W} * {cnext}", *bounds, chain=chain, proof=proof)
    def bind(self, base, code, nat, skip=False):
        self.k += 1
        name = f"{base}{self.k}"
        self.binds.append((name, code, nat))
        if skip:
            self.skip.add(name)
        return name

def lsum(names):
    return " + ".join(f"{N(x)} * 2^{W * j}" for j, x in enumerate(names))

def P_(x):
    return f"({x})"

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
        x = g.bind("x", code, nat, skip=True)
        dj = g.bind("d", f"{x} &&& {M}", f"{N(x)} % 2^{W}", skip=True)
        w = g.bind("w", f"{x} >>> 63", f"{N(x)} / 2^63", skip=True)
        ht = f"@B[{N(t[j])} < 2^{W}]"
        proof = (f"sub_limb_b {t[j]} {P[j]} {bw} {ht} (by decide) {g.bnd(bw, 1)}" if bw
                 else f"sub_limb {t[j]} {P[j]} {ht} (by decide)")
        g.eqn("fs", f"{N(dj)} + {P[j]}", N(bw) if bw else "0", N(t[j]), N(w),
              (f"{N(dj)} < 2^{W}", True), (f"{N(w)} ≤ 1", j == n - 1), proof=proof)
        d.append(dj); bw = w
    cond = f"{bw} == 0" if top is None else f"{top} != 0 || {bw} == 0"
    g.fsw = bw
    return cond, d, t

def gen_mul(n, p, n0, square):
    g = Gen()
    P = limbs(p, n)
    ms, r, acc = [], [], None
    for k in range(2 * n - 1):
        cprev = acc
        code, nat = column_code(g, k, n, P, ms, acc, square)
        _, natnc = column_code(g, k, n, P, ms, None, square)
        s = g.bind("s", code, nat)
        if k < n:
            m = g.bind("m", f"({s} * {n0}) &&& {M}", f"({N(s)} * {n0}) % 2^{W}")
            ms.append(m)
            s2 = g.bind("s", f"{s} + {m} * {P[0]}", f"{N(s)} + {N(m)} * {P[0]}")
            acc = g.bind("c", f"{s2} >>> {W}", f"{N(s2)} / 2^{W}")
            g.eqn("mul", f"{natnc} + {N(m)} * {P[0]}", N(cprev) if cprev else "0", "0", N(acc),
                  (f"{N(m)} < 2^{W}", True), f"{N(acc)} < 2^37")
        else:
            rk = g.bind("r", f"{s} &&& {M}", f"{N(s)} % 2^{W}")
            r.append(rk)
            acc = g.bind("c", f"{s} >>> {W}", f"{N(s)} / 2^{W}")
            g.eqn("mul", natnc, N(cprev), N(rk), N(acc),
                  (f"{N(rk)} < 2^{W}", True), (f"{N(acc)} < 2^37", k == 2 * n - 2))
    r.append(acc)
    if square:
        expn = " + ".join((f"a.l{i}.toNat * a.l{i}.toNat * 2^{2 * W * i}" if i == j else
                          f"a.l{i}.toNat * a.l{j}.toNat * 2 * 2^{W * (i + j)}")
                         for i in range(n) for j in range(i, n))
    else:
        expn = " + ".join(f"a.l{i}.toNat * b.l{j}.toNat * 2^{W * (i + j)}" for i in range(n) for j in range(n))
    g.expansion = expn
    g.rlimbs = r
    g.mid_index = len(g.binds)
    cond, d, t = final_sub(g, n, P, r, None)
    return g, cond, d, t, ms

def gen_add(n, p):
    g = Gen()
    P = limbs(p, n)
    c, t = None, []
    for j in range(n):
        cp = c
        code = f"a.l{j} + b.l{j}" + (f" + {c}" if c else "")
        nat = f"a.l{j}.toNat + b.l{j}.toNat" + (f" + {N(c)}" if c else "")
        s = g.bind("s", code, nat)
        tj = g.bind("t", f"{s} &&& {M}", f"{N(s)} % 2^{W}")
        t.append(tj)
        c = g.bind("c", f"{s} >>> {W}", f"{N(s)} / 2^{W}")
        g.eqn("add", f"a.l{j}.toNat + b.l{j}.toNat", N(cp) if cp else "0", N(tj), N(c),
              (f"{N(tj)} < 2^{W}", True), (f"{N(c)} ≤ 1", j == n - 1))
    g.top = c
    cond, d, tt = final_sub(g, n, P, t, c)
    return g, cond, d, tt

def gen_sub(n, p):
    g = Gen()
    P = limbs(p, n)
    bw, d = None, []
    for j in range(n):
        code = f"a.l{j} - b.l{j}" + (f" - {bw}" if bw else "")
        nat = f"(a.l{j}.toNat + 2^65 - b.l{j}.toNat" + (f" - {N(bw)}" if bw else "") + ") % 2^64"
        x = g.bind("x", code, nat, skip=True)
        dj = g.bind("d", f"{x} &&& {M}", f"{N(x)} % 2^{W}", skip=True)
        d.append(dj)
        w = g.bind("w", f"{x} >>> 63", f"{N(x)} / 2^63", skip=True)
        proof = (f"sub_limb_b a.l{j} b.l{j} {bw} ha{j} hb{j} {g.bnd(bw, 1)}" if bw
                 else f"sub_limb a.l{j} b.l{j} ha{j} hb{j}")
        g.eqn("sub", f"{N(dj)} + b.l{j}.toNat", N(bw) if bw else "0", f"a.l{j}.toNat", N(w),
              (f"{N(dj)} < 2^{W}", True), (f"{N(w)} ≤ 1", True), proof=proof)
        bw = w
    c, e = None, []
    for j in range(n):
        cp = c
        code = f"{d[j]} + {P[j]}" + (f" + {c}" if c else "")
        nat = f"{N(d[j])} + {P[j]}" + (f" + {N(c)}" if c else "")
        s = g.bind("s", code, nat)
        tj = g.bind("t", f"{s} &&& {M}", f"{N(s)} % 2^{W}")
        e.append(tj)
        c = g.bind("c", f"{s} >>> {W}", f"{N(s)} / 2^{W}")
        g.eqn("addp", f"{N(d[j])} + {P[j]}", N(cp) if cp else "0", N(tj), N(c),
              (f"{N(tj)} < 2^{W}", True), (f"{N(c)} ≤ 1", j == n - 1))
    g.sbw = bw
    g.top = c
    return g, f"{bw} == 0", d, e

def emit_code(L, g, cond, d, t):
    for name, code, _ in g.binds:
        L.append(f"  let {name} := {code}")
    L.append(f"  if {cond} then ⟨{', '.join(d)}⟩ else ⟨{', '.join(t)}⟩")

def emit_facts(L, g, ind="  ", drop=(), mid=None):
    """One `have` per binding (its Nat value, below 2^64); after each group, its clean linear
    facts, its step of its carry chain (the generic lemma `chain`), and then the raw facts and
    the chain's previous step are cleared, so no `omega` call sees more than a few facts with
    truncated subtractions or remainders. At the end, everything but the bounds the conclusion
    needs and the last step of each chain is cleared."""
    gi = 0
    pending = []
    cnt = 0
    last = {}
    steps = {}
    factname = g.factname
    grp_vars = []
    pscnt = 0
    for idx, (name, code, nat) in enumerate(g.binds):
        grp_vars.append(name)
        if name not in g.skip:
            L.append(f"{ind}have h_{name} : {name}.toNat = {nat} := by simp only [{name}, {SIMP}] <;> omega")
            L.append(f"{ind}have l_{name} := UInt64.toNat_lt {name}")
            pending += [f"h_{name}", f"l_{name}"]
        while gi < len(g.groups) and g.groups[gi][0] == idx + 1:
            _, facts, ch, proof = g.groups[gi]
            eqname = None
            if proof is not None:
                import re as _re
                proof = _re.sub(r"@B\[([^\]]*)\]", lambda m_: factname[m_.group(1)], proof)
                names = [f"k{cnt + 1 + i}" for i in range(len(facts))]
                texts = [f[0] if isinstance(f, tuple) else f for f in facts]
                L.append(f"{ind}obtain ⟨{', '.join(names)}⟩ : {' ∧ '.join(texts)} := {proof}")
            for fi, fact in enumerate(facts):
                cnt += 1
                text, keep = fact if isinstance(fact, tuple) else (fact, False)
                factname[text] = f"k{cnt}"
                if proof is None:
                    L.append(f"{ind}have k{cnt} : {text} := by omega")
                if ch is not None and fi == 0:
                    eqname = f"k{cnt}"
                elif not keep:
                    g.dropped.append(f"k{cnt}")
                else:
                    g.kept.append((f"k{cnt}", text))
            if pending:
                L.append(f"{ind}clear {' '.join(pending)}")
            pending = []

            if ch is not None:
                pscnt += 1
                prev = last.get(ch)
                h1 = prev if prev else "(I := 0) (O := 0) (c := 0) (B := 1) rfl"
                step = steps.get(ch, 0) + 1
                steps[ch] = step
                L.append(f"{ind}have ps{pscnt} := chain (B' := 2^{W * step}) {h1} {eqname} (by decide)")
                L.append(f"{ind}clear {eqname}" + (f" {prev}" if prev else ""))
                last[ch] = f"ps{pscnt}"
            gi += 1
        if mid is not None and mid[0] == idx + 1:
            mid[1](L, ind, last)
    L.append(f"{ind}clear_value {' '.join(nm for nm, _, _ in g.binds)}")
    dr = list(g.dropped) + list(drop)
    if dr:
        L.append(f"{ind}clear {' '.join(dr)}")
    if last:
        L.append(f"{ind}unfold Hide at {' '.join(last.values())}")
    return last
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

def emit_bound(L, g, nm, limbs_, ind="  "):
    """`nm_{n-1} : Σ limbs < 2^(Wn)` from the limb bounds, through `bfirst`/`bstep`."""
    bound_of = {text: k for k, text in g.kept}
    prev = None
    for j, x in enumerate(limbs_):
        hb = bound_of[f"{N(x)} < 2^{W}"]
        if j == 0:
            L.append(f"{ind}have {nm}_0 : {N(x)} * 2^0 < 2^{W} := bfirst {hb}")
        else:
            part = lsum(limbs_[:j + 1])
            L.append(f"{ind}have {nm}_{j} : {part} < 2^{W * (j + 1)} := bstep {nm}_{j - 1} {hb} (by decide)")
        if prev: L.append(f"{ind}clear {prev}")
        prev = f"{nm}_{j}"
    return prev

def finish(L, g, last, n, base_hyps, eqs, bounded, fin, res1, res2, ind="  "):
    """The conclusion, from the last step of each carry chain:
    * `eqs`: (name, statement) sum identities, each proved by `grind` from the chain steps alone
      (everything else cleared);
    * `bounded`: lists of limbs whose sums are bounded by R through `bfirst`/`bstep`, named bd0, bd1, …;
    * `fin`: the final lemma (`add_fin`, `sub_fin`, `mul_fin`) applied to these, with `{bdK}` for the
      bound names and `{F:text}` for the name of the kept fact `text`;
    * `res1`, `res2`: the limbs of the result in the two branches of the final comparison."""
    bnames = [nm for nm, _ in g.kept]
    allh = list(base_hyps) + bnames
    chains = list(last.values())
    for nm, st in eqs:
        L.append(f"{ind}have {nm} : {st} := by")
        L.append(f"{ind}  clear {' '.join(allh)}")
        L.append(f"{ind}  grind")
    L.append(f"{ind}clear {' '.join(chains)}")
    bds = []
    for bi, limbs_ in enumerate(bounded):
        bds.append(emit_bound(L, g, f"bd{bi}", limbs_, ind))
    import re as _re
    call = fin
    for bi, nm in enumerate(bds):
        call = call.replace("{bd%d}" % bi, nm)
    call = _re.sub(r"\{F:([^}]*)\}", lambda m_: g.factname[m_.group(1)], call)
    lim = lambda rs: ", ".join(g.factname[f"{N(x)} < 2^{W}"] for x in rs)
    L.append(f"{ind}split <;> rename_i hc <;>")
    L.append(f"{ind}  simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq, ← UInt64.toNat_inj, UInt64.reduceToNat, Bool.not_eq_true'] at hc <;>")
    L.append(f"{ind}  simp only [Elem.Ok, Elem.val, p]")
    L.append(f"{ind}· have h := ({call}).1 hc")
    L.append(f"{ind}  exact ⟨⟨{lim(res1)}, h.1⟩, h.2⟩")
    L.append(f"{ind}· have h := ({call}).2 hc")
    L.append(f"{ind}  exact ⟨⟨{lim(res2)}, h.1⟩, h.2⟩")

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
    w("import JamCrypto.Fast.FieldClass")
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
        w(f"  generalize hE0 : {g.expansion} = E at hABlt ⊢")
        w(f"  have hE : Hide ({g.expansion} = E) := hE0")
        w(f"  clear hE0")
        for i in range(n):
            for j in range(n):
                if sq and j < i: continue
                w(f"  have hp{i}_{j} := mul_lt29 ha{i} h{bs}{j}")
        w(f"  simp only [R, p]")
        w(f"  unfold {fname}")
        w("  extract_lets " + " ".join(nm for nm, _, _ in g.binds))
        hps = [f"hp{i}_{j}" for i in range(n) for j in range(n) if not (sq and j < i)]
        base = [f"ha{j}" for j in range(n)] + ["hav", "hABlt", "hE"] + ([] if sq else [f"hb{j}" for j in range(n)] + ["hbv"])
        rl = g.rlimbs
        acc = rl[-1]
        def mid(L, ind, last, g=g, rl=rl, acc=acc, ms=ms, hps=hps, base=base):
            # T·R = a·b + M·p, M < R and a·b < p² give T < 2p, hence the last carry is a limb
            ps = last.pop("mul")
            L.append(f"{ind}unfold Hide at {ps}")
            L.append(f"{ind}clear {' '.join(hps)}")
            kept = [k for k, _ in g.kept]
            L.append(f"{ind}have e1 : ({lsum(rl)}) * 2^{W * n} = E + ({lsum(ms)}) * {p} := by")
            L.append(f"{ind}  clear {' '.join(b for b in base if b != 'hE')} {' '.join(kept)}")
            L.append(f"{ind}  unfold Hide at hE")
            L.append(f"{ind}  omega")
            L.append(f"{ind}clear {ps} hE")
            L.append(f"{ind}have e3 : {N(acc)} * 2^{W * (n - 1)} ≤ ({lsum(rl)}) := by")
            L.append(f"{ind}  clear {' '.join(b for b in base if b != 'hE')} {' '.join(kept)} e1")
            L.append(f"{ind}  omega")
            bm = emit_bound(L, g, "bm", ms, ind)
            L.append(f"{ind}have hacc : {N(acc)} < 2^{W} := carry_lt e1 e3 hABlt {bm} (by decide) (by decide)")
            L.append(f"{ind}clear e3")
            g.kept.append(("hacc", f"{N(acc)} < 2^{W}"))
            g.factname[f"{N(acc)} < 2^{W}"] = "hacc"
            g.kept.append(("e1", "e1"))
            g.kept.append((bm, "bm"))
        last = emit_facts(L, g, mid=(g.mid_index, mid))
        finish(L, g, last, n, [b for b in base if b != "hE"],
               [("e2", f"({lsum(d)}) + {p} = ({lsum(rl)}) + 2^{W * n} * {N(g.fsw)}")],
               [d],
               "mul_fin e1 e2 hABlt bm_%d {bd0} {F:%s} (by decide)" % (n - 1, f"{N(g.fsw)} ≤ 1"),
               d, rl)
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
    last = emit_facts(L, g)
    base = [f"ha{j}" for j in range(n)] + ["hav"] + [f"hb{j}" for j in range(n)] + ["hbv"]
    finish(L, g, last, n, base,
           [("e1", f"({lsum(t)}) + 2^{W * n} * {N(g.top)} = ({val_expr('a', n)}) + ({val_expr('b', n)})"),
            ("e2", f"({lsum(d)}) + {p} = ({lsum(t)}) + 2^{W * n} * {N(g.fsw)}")],
           [d],
           "add_fin e1 e2 hav hbv {bd0} {F:%s} {F:%s} (by decide)" % (f"{N(g.top)} ≤ 1", f"{N(g.fsw)} ≤ 1"),
           d, t)
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
    last = emit_facts(L, g)
    base = [f"ha{j}" for j in range(n)] + ["hav"] + [f"hb{j}" for j in range(n)] + ["hbv"]
    finish(L, g, last, n, base,
           [("e1", f"({lsum(d)}) + ({val_expr('b', n)}) = ({val_expr('a', n)}) + 2^{W * n} * {N(g.sbw)}"),
            ("e2", f"({lsum(t)}) + 2^{W * n} * {N(g.top)} = ({lsum(d)}) + {p}")],
           [d, t],
           "sub_fin e1 e2 hav hbv {bd0} {bd1} {F:%s} {F:%s} (by decide)" % (f"{N(g.sbw)} ≤ 1", f"{N(g.top)} ≤ 1"),
           d, t)
    w("")
    t = TMPL
    horner = "a.l0.toNat"
    for j in range(n - 1, 0, -1):
        pass
    def hor(pre, j):
        return f"{pre}.l{j}.toNat" if j == n - 1 else f"{pre}.l{j}.toNat + 2^{W} * ({hor(pre, j + 1)})"
    inj = []
    for j in range(n - 1):
        inj.append(f"  obtain ⟨e{j}, h⟩ := limb_inj ha{j} hb{j} h")
    inj.append(f"  have e{n-1} := h")
    subs = {
        "@@HS@@": ", ".join(f"_" for j in range(n)),
        "@@BEQ@@": " && ".join(f"a.l{j} == b.l{j}" for j in range(n)),
        "@@ISZ@@": " && ".join(f"a.l{j} == 0" for j in range(n)),
        "@@HORNER@@": hor("a", 0),
        "@@HORNERM@@": hor("m", 0),
        "@@HA@@": ", ".join(f"ha{j}" for j in range(n)),
        "@@HB@@": ", ".join(f"hb{j}" for j in range(n)),
        "@@INJ@@": "\n".join(inj),
        "@@EXS@@": ", ".join(f"UInt64.toNat_inj.mp e{j}" for j in range(n)),
        "@@HPROJ@@": ", ".join(f"h.{'2.' * j}{'1' if j < n - 1 else ''}".rstrip('.') for j in range(n)),
        "@@WN@@": str(W * n),
        "@@RAW@@": "⟨" + ", ".join(f"UInt64.ofNat (x / 2^{W * j} % 2^{W})" for j in range(n)) + "⟩",
        "@@RAWB@@": ", ".join("Nat.mod_lt _ (by decide)" for j in range(n)),
        "@@N@@": str(n),
        "@@NAME@@": name,
    }
    for k, v in subs.items():
        t = t.replace(k, v)
    L.append(t)
    w(f"end JamCrypto.Fast.{name}")
    return "\n".join(L) + "\n"

TMPL = r'''
/-! ## Derived operations and their values -/

theorem Elem.Ok.val_lt {a : Elem} (h : a.Ok) : a.val < p := by
  obtain ⟨@@HS@@, hv⟩ := h; exact hv

theorem p_pos : 0 < p := by decide

theorem value_lt (a : Elem) : a.value < p := Nat.mod_lt _ p_pos

theorem zero_ok : zero.Ok := by unfold Elem.Ok Elem.val zero p; decide
theorem one_ok : one.Ok := by unfold Elem.Ok Elem.val one p; decide
theorem r2_ok : r2.Ok := by unfold Elem.Ok Elem.val r2 p; decide
theorem raw1_ok : raw1.Ok := by unfold Elem.Ok Elem.val raw1 p; decide

theorem zero_val : zero.val = 0 := by unfold Elem.val zero; decide
theorem raw1_val : raw1.val = 1 := by unfold Elem.val raw1; decide
theorem value_zero : zero.value = 0 := by unfold Elem.value; rw [zero_val]; rfl
theorem value_one : one.value = 1 := by unfold Elem.value Elem.val one rInv p; decide
theorem r2_val : r2.val = R * R % p := by unfold Elem.val r2 R p; decide

theorem ok_mul {a b : Elem} (ha : a.Ok) (hb : b.Ok) : (mul a b).Ok := (mul_spec a b ha hb).1
theorem value_mul {a b : Elem} (ha : a.Ok) (hb : b.Ok) :
    (mul a b).value = a.value * b.value % p := mont_mul_value R_rInv (mul_spec a b ha hb).2
theorem ok_sq {a : Elem} (ha : a.Ok) : (sq a).Ok := (sq_spec a ha).1
theorem value_sq {a : Elem} (ha : a.Ok) : (sq a).value = a.value * a.value % p :=
  mont_mul_value R_rInv (sq_spec a ha).2
theorem ok_add {a b : Elem} (ha : a.Ok) (hb : b.Ok) : (add a b).Ok := (add_spec a b ha hb).1
theorem value_add {a b : Elem} (ha : a.Ok) (hb : b.Ok) :
    (add a b).value = (a.value + b.value) % p := mont_add_value (add_spec a b ha hb).2
theorem ok_sub {a b : Elem} (ha : a.Ok) (hb : b.Ok) : (sub a b).Ok := (sub_spec a b ha hb).1
theorem value_sub {a b : Elem} (ha : a.Ok) (hb : b.Ok) :
    (sub a b).value = (a.value + p - b.value) % p :=
  mont_sub_value p_pos (sub_spec a b ha hb).2 hb.val_lt

/-- −a. -/
@[inline] def neg (a : Elem) : Elem := sub zero a
/-- 2a. -/
@[inline] def dbl (a : Elem) : Elem := add a a

theorem ok_neg {a : Elem} (ha : a.Ok) : (neg a).Ok := ok_sub zero_ok ha
theorem value_neg {a : Elem} (ha : a.Ok) : (neg a).value = (p - a.value) % p := by
  unfold neg; rw [value_sub zero_ok ha, value_zero, Nat.zero_add]
theorem ok_dbl {a : Elem} (ha : a.Ok) : (dbl a).Ok := ok_add ha ha
theorem value_dbl {a : Elem} (ha : a.Ok) : (dbl a).value = (a.value + a.value) % p := value_add ha ha

/-- Equality (elements are reduced, so limbwise). -/
def beq (a b : Elem) : Bool :=
  @@BEQ@@

/-- a = 0. -/
def isZero (a : Elem) : Bool :=
  @@ISZ@@

instance : BEq Elem := ⟨beq⟩
instance : Add Elem := ⟨add⟩
instance : Sub Elem := ⟨sub⟩
instance : Mul Elem := ⟨mul⟩
instance : Neg Elem := ⟨neg⟩

theorem val_horner (a : Elem) : a.val = @@HORNER@@ := by
  simp only [Elem.val]; omega

theorem val_inj {a b : Elem} (ha : a.Ok) (hb : b.Ok) (h : a.val = b.val) : a = b := by
  rw [val_horner, val_horner] at h
  obtain ⟨@@HA@@, _⟩ := ha
  obtain ⟨@@HB@@, _⟩ := hb
@@INJ@@
  cases a; cases b
  simp only [Elem.mk.injEq]
  exact ⟨@@EXS@@⟩

theorem value_inj {a b : Elem} (ha : a.Ok) (hb : b.Ok) (h : a.value = b.value) : a = b :=
  val_inj ha hb (mont_inj R_rInv ha.val_lt hb.val_lt h)

theorem beq_eq_true {a b : Elem} (h : beq a b = true) : a = b := by
  cases a; cases b
  simp only [beq, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  simp only [Elem.mk.injEq]
  exact ⟨@@HPROJ@@⟩

theorem beq_self (a : Elem) : beq a a = true := by
  simp [beq]

/-- `beq` decides equality of values. -/
theorem beq_eq {a b : Elem} (ha : a.Ok) (hb : b.Ok) : beq a b = (a.value == b.value) := by
  by_cases hv : a.value = b.value
  · rw [value_inj ha hb hv, beq_self]; simp
  · have : beq a b = false := by
      cases h : beq a b
      · rfl
      · exact absurd (by rw [beq_eq_true h]) hv
    rw [this]; simp [hv]

theorem isZero_eq_beq (a : Elem) : isZero a = beq a zero := by
  simp [isZero, beq, zero]

/-- `isZero` decides whether the value is 0. -/
theorem isZero_eq {a : Elem} (ha : a.Ok) : isZero a = (a.value == 0) := by
  rw [isZero_eq_beq, beq_eq ha zero_ok, value_zero]

/-- The limbs of x mod 2^@@WN@@ (not in Montgomery form). -/
def rawOfNat (x : Nat) : Elem :=
  @@RAW@@

theorem rawOfNat_spec {x : Nat} (hx : x < p) : (rawOfNat x).Ok ∧ (rawOfNat x).val = x := by
  have hd := digitSum_eq x @@N@@
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide))] at hd
  simp only [digitSum, Nat.zero_add, ← Nat.pow_mul, Nat.reduceMul] at hd
  simp only [rawOfNat, Elem.Ok, Elem.val, UInt64.toNat_ofNat', mod29_mod64]
  refine ⟨⟨@@RAWB@@, ?_⟩, hd⟩
  rw [hd]; exact hx

/-- The element with value x mod p. -/
def ofNat (x : Nat) : Elem := mul (rawOfNat (x % p)) r2

theorem ok_ofNat (x : Nat) : (ofNat x).Ok :=
  ok_mul (rawOfNat_spec (Nat.mod_lt x p_pos)).1 r2_ok

theorem r2_value : r2.value = R % p := by unfold Elem.value Elem.val r2 rInv R p; decide

theorem value_ofNat (x : Nat) : (ofNat x).value = x % p := by
  have h1 := rawOfNat_spec (Nat.mod_lt x p_pos)
  unfold ofNat
  rw [value_mul h1.1 r2_ok, r2_value]
  unfold Elem.value
  rw [h1.2, ← Nat.mul_mod, Nat.mul_assoc, Nat.mul_comm rInv R, mod_mul_one R_rInv, Nat.mod_mod]

/-- The value (below p) of an element. -/
def toNat (a : Elem) : Nat := (mul a raw1).val

theorem toNat_eq {a : Elem} (ha : a.Ok) : toNat a = a.value := by
  have h := mul_spec a raw1 ha raw1_ok
  rw [raw1_val, Nat.mul_one] at h
  exact mont_of_mul R_rInv h.1.val_lt h.2

/-- The value of an element is odd. -/
def isOdd (a : Elem) : Bool := (mul a raw1).l0 &&& 1 == 1

theorem isOdd_eq {a : Elem} (ha : a.Ok) : isOdd a = (a.value % 2 == 1) := by
  rw [← toNat_eq ha]
  unfold isOdd toNat
  rw [val_horner]
  generalize mul a raw1 = m
  have h1 : (@@HORNERM@@) % 2 = m.l0.toNat % 2 := by omega
  rw [h1]
  have e : (m.l0 &&& 1).toNat = m.l0.toNat % 2 := by
    rw [UInt64.toNat_and]; exact Nat.and_one_is_mod _
  by_cases hb : m.l0.toNat % 2 = 1
  · have : m.l0 &&& 1 = 1 := UInt64.toNat_inj.mp (by rw [e, hb]; rfl)
    simp [this, hb]
  · have : m.l0 &&& 1 ≠ 1 := fun h => hb (by rw [← e, h]; rfl)
    have h2 : (m.l0 &&& 1 == 1) = false := by simpa using this
    have h3 : (m.l0.toNat % 2 == 1) = false := by simpa using hb
    rw [h2, h3]

/-- The bits of e, most significant first (empty for 0). -/
def bitsMsb (e : Nat) : Array Bool := Id.run do
  let n := if e == 0 then 0 else e.log2 + 1
  let mut out : Array Bool := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (e.testBit (n - 1 - i))
  return out

/-- a^e for e given by its bits, most significant first. -/
def powBits (a : Elem) (bits : Array Bool) : Elem := Id.run do
  let mut r := one
  for b in bits do
    r := sq r
    if b then r := mul r a
  return r

/-- a^e. -/
def pow (a : Elem) (e : Nat) : Elem := powBits a (bitsMsb e)

def pMinus2Bits : Array Bool := bitsMsb (p - 2)

/-- a⁻¹ (Fermat: a^(p−2)); 0 for 0. -/
def inv (a : Elem) : Elem := powBits a pMinus2Bits

def halfBits : Array Bool := bitsMsb ((p - 1) / 2)

/-- a is a nonzero square (Euler's criterion). -/
def isSquare (a : Elem) : Bool := powBits a halfBits == one

instance : Field Elem where
  p := p
  zero := zero
  one := one
  add := add
  sub := sub
  mul := mul
  sq := sq
  ofNat := ofNat
  toNat := toNat
  beq := beq
  isZero := isZero
  Ok := Elem.Ok
  value := Elem.value

instance : LawfulField Elem where
  one_lt_p := by decide
  ok_zero := zero_ok
  ok_one := one_ok
  value_zero := value_zero
  value_one := value_one
  value_lt := value_lt
  ok_add := ok_add
  ok_sub := ok_sub
  ok_mul := ok_mul
  ok_sq := ok_sq
  ok_ofNat := ok_ofNat
  value_add := value_add
  value_sub := value_sub
  value_mul := value_mul
  value_sq := value_sq
  value_ofNat := value_ofNat
  toNat_eq := toNat_eq
  beq_eq := beq_eq
  isZero_eq := isZero_eq

@[inline] def Elem.toNat (a : Elem) : Nat := JamCrypto.Fast.@@NAME@@.toNat a
@[inline] def Elem.isZero (a : Elem) : Bool := JamCrypto.Fast.@@NAME@@.isZero a
@[inline] def Elem.inv (a : Elem) : Elem := JamCrypto.Fast.@@NAME@@.inv a
@[inline] def Elem.sq (a : Elem) : Elem := JamCrypto.Fast.@@NAME@@.sq a
'''

def main():
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    import sys
    # Fq (14 limbs) is not generated by default yet: its proofs exceed the memory of the build
    # machines; generate it explicitly with `field.py Fq` (work in progress for the ring).
    only = sys.argv[1:] or ["Fr", "Fp25519"]
    for name, doc, p in FIELDS:
        if name in only:
            with open(os.path.join(root, f"{name}.lean"), "w") as f:
                f.write(gen_module(name, doc, p))

main()
