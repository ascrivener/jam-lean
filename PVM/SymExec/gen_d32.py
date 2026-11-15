#!/usr/bin/env python3
"""Generate executor checks of <u32 as Display>::fmt (68146 -> 61857) per digit-count range."""
import sys
T64 = 2**64
BASE = ['y','sp','v','F','ret','v5','v6']
BASE_UB = [None, 2**32, 2**32-4, 2**32, 2807, T64, T64]
BASE_LB = [None, 2147484248, 0, 0, 2, 0, 0]

class Gen:
    def __init__(self, lo, hi):
        self.lo, self.hi = lo, hi
        self.names = list(BASE); self.ub = list(BASE_UB); self.lb = list(BASE_LB)
        self.ub[0], self.lb[0] = hi, lo
        self.rws = []; self.defs = []   # defs: (k, lean expr over vals)
    def var(self, name, lo, hi, expr):
        k = len(self.names); self.names.append(name); self.lb.append(lo); self.ub.append(hi); self.defs.append((k, expr)); return k
    def rw(self, pat, k): self.rws.append((pat, k))
    # one-op helpers; x is a var index, (lo,hi) inclusive-exclusive value range of x
    def loop(self, x, xr, sx=False):
        lo, hi = xr
        xs = f'(.sx 4 (.var {x}))' if sx else f'(.var {x})'
        a = self.var('a', lo*2**32, (hi-1)*2**32+1, f'v{x} * 4294967296'); self.rw(f'.alu2i .shloLImm64 (.const 0) {xs} 32', a)
        M = 15111572745684516864
        b = self.var('b', lo*2**32*M//T64, (hi-1)*2**32*M//T64+1, f'v{a} * {M} / {T64}'); self.rw(f'.alu3 .mulUpperUU (.var {a}) (.const {M}) (.const 0)', b)
        q = self.var('q', lo//10000, (hi-1)//10000+1, f'v{x} / 10000'); self.rw(f'.alu2i .shloRImm64 (.const 0) (.var {b}) 45', q)
        c = self.var('c', lo//10000*10000, (hi-1)//10000*10000+1, f'v{x} / 10000 * 10000'); self.rw(f'.alu3 .mul64 (.var {q}) (.const 10000) (.const 0)', c)
        if sx:
            r = self.var('r', 0, T64, f'v{x} + 18446744069414584320 - v{x} / 10000 * 10000'); self.rw(f'.alu3 .sub64 {xs} (.var {c}) (.const 0)', r)
            d = self.var('d', 0, 10000*2**48, f'v{x} % 10000 * 281474976710656'); self.rw(f'.alu2i .shloLImm64 (.const 0) (.var {r}) 48', d)
        else:
            r = self.var('r', 0, 10000, f'v{x} % 10000'); self.rw(f'.alu3 .sub64 (.var {x}) (.var {c}) (.const 0)', r)
            d = self.var('d', 0, 10000*2**48, f'v{x} % 10000 * 281474976710656'); self.rw(f'.alu2i .shloLImm64 (.const 0) (.var {r}) 48', d)
        e = self.var('e', 0, 2500, f'v{x} % 10000 / 4'); self.rw(f'.alu2i .shloRImm64 (.const 0) (.var {d}) 50', e)
        f = self.var('f', 0, 2500*5243, f'v{x} % 10000 / 4 * 5243'); self.rw(f'.alu3 .mul64 (.var {e}) (.const 5243) (.const 0)', f)
        g = self.var('g', 0, 201, f'v{x} % 10000 / 4 * 5243 / 65536'); self.rw(f'.alu2i .shloRImm64 (.const 0) (.var {f}) 16', g)
        hiI = self.var('hiIdx', 0, 199, f'2 * (v{x} % 10000 / 100)'); self.rw(f'.alu2i .andImm (.const 0) (.var {g}) 2046', hiI)
        h = self.var('h', 0, 100, f'v{x} % 10000 / 100'); self.rw(f'.alu2i .shloRImm64 (.const 0) (.var {f}) 17', h)
        i = self.var('i', 0, 9901, f'v{x} % 10000 / 100 * 100'); self.rw(f'.alu2i .mulImm64 (.const 0) (.var {h}) 100', i)
        if sx:
            j = self.var('j', 0, T64, f'v{x} + 18446744069414584320 - v{x} / 10000 * 10000 - v{x} % 10000 / 100 * 100'); self.rw(f'.alu3 .sub64 (.var {r}) (.var {i}) (.const 0)', j)
        else:
            j = self.var('j', 0, 100, f'v{x} % 100'); self.rw(f'.alu3 .sub64 (.var {r}) (.var {i}) (.const 0)', j)
        kk = self.var('k', 0, 100*2**49, f'v{x} % 100 * 562949953421312'); self.rw(f'.alu2i .shloLImm64 (.const 0) (.var {j}) 49', kk)
        loI = self.var('loIdx', 0, 199, f'2 * (v{x} % 100)'); self.rw(f'.alu2i .shloRImm64 (.const 0) (.var {kk}) 48', loI)
        return q, (lo//10000, (hi-1)//10000+1), hiI, loI
    def short(self, x, xr):
        lo, hi = xr
        out = {}
        if hi > 10:
            d = self.var('sd', lo*2**48, (hi-1)*2**48+1, f'v{x} * 281474976710656'); self.rw(f'.alu2i .shloLImm64 (.const 0) (.var {x}) 48', d)
            e = self.var('se', lo//4, (hi-1)//4+1, f'v{x} / 4'); self.rw(f'.alu2i .shloRImm64 (.const 0) (.var {d}) 50', e)
            f = self.var('sf', lo//4*5243, (hi-1)//4*5243+1, f'v{x} / 4 * 5243'); self.rw(f'.alu2i .mulImm64 (.const 0) (.var {e}) 5243', f)
            h = self.var('hund', lo//100, (hi-1)//100+1, f'v{x} / 100'); self.rw(f'.alu2i .shloRImm64 (.const 0) (.var {f}) 17', h)
            i = self.var('si', lo//100*100, (hi-1)//100*100+1, f'v{x} / 100 * 100'); self.rw(f'.alu2i .mulImm64 (.const 0) (.var {h}) 100', i)
            j = self.var('sj', 0, 100, f'v{x} % 100'); self.rw(f'.alu3 .sub64 (.var {x}) (.var {i}) (.const 0)', j)
            kk = self.var('sk', 0, 100*2**49, f'v{x} % 100 * 562949953421312'); self.rw(f'.alu2i .shloLImm64 (.const 0) (.var {j}) 49', kk)
            two = self.var('twoIdx', 0, 199, f'2 * (v{x} % 100)'); self.rw(f'.alu2i .shloRImm64 (.const 0) (.var {kk}) 48', two)
            out['two'] = two
            if lo >= 100:
                lead = self.var('lead', 2*(lo//100), 2*((hi-1)//100)+1, f'2 * (v{x} / 100)'); self.rw(f'.alu2i .shloLImm32 (.const 0) (.var {h}) 1', lead); out['lead'] = lead
        else:
            lead = self.var('lead', 2*lo, 2*(hi-1)+1, f'2 * v{x}'); self.rw(f'.alu2i .shloLImm32 (.const 0) (.var {x}) 1', lead); out['lead'] = lead
        return out

def emit(tag, g):
    tag = str(tag)
    ub = ', '.join(str(u) for u in g.ub); lb = ', '.join(str(l) for l in g.lb)
    rws = ',\n    '.join(f'({p}, .var {k})' for p, k in g.rws)
    return f'''
def st_{tag} : Static :=
  {{ ub := [{ub}]
    lb := [{lb}]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [{rws}] }}
#eval match (List.range 140).find? (fun k => (traceRun st_{tag} Services.Bootstrap.SymExec.progF k 68146 (init A)).2.map (·.1) == some 61857) with
  | some k => match (traceRun st_{tag} Services.Bootstrap.SymExec.progF k 68146 (init A)).2 with
    | some (_, σ) => s!"RANGE {tag} STEPS {{k}} R11 {{repr (σ.regs.getD 11 (.const 0))}} R12 {{repr (σ.regs.getD 12 (.const 0))}} CELLS {{repr (σ.cells.filter fun (c : Aff × Nat × SVal) => c.1.base == some 1 && decide ((-40 : Int) ≤ c.1.off) && decide (c.1.off < (-24 : Int)))}}"
    | none => "none"
  | none => "none"
'''

def build(lo, hi):
    g = Gen(lo, hi)
    x, xr = 0, (lo, hi)
    groups = 0
    while xr[0] >= 1000:
        q, qr, hiI, loI = g.loop(x, xr, sx=(groups == 0 and lo >= 2**31)); x, xr = q, qr; groups += 1
        if xr[1] <= 1: break
    if groups == 0 or not (xr[0] == 0 and xr[1] == 1):
        g.short(x, xr)
    return g

if __name__ == '__main__':
    ranges = [(0,1),(1,10),(10,100),(100,1000),(1000,10000),(10000,100000),(100000,1000000),(1000000,10000000),(10000000,100000000),(100000000,1000000000),(1000000000,2**31),(2**31,2**32)]
    out = open(sys.argv[1]).read().split('-- GENERATED')[0] + '-- GENERATED\n'
    for lo, hi in ranges:
        g = Gen(lo, hi)
        x, xr = 0, (lo, hi)
        groups = 0
        while xr[0] >= 1000:
            q, qr, hiI, loI = g.loop(x, xr, sx=(groups == 0 and lo >= 2**31)); x, xr = q, qr; groups += 1
            if xr[1] <= 1: break
        if groups == 0 or not (xr[0] == 0 and xr[1] == 1):
            g.short(x, xr)
        out += emit(f'{lo}', g)
    open(sys.argv[1], 'w').write(out)
    print('ok')
    
