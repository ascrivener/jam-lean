"""Interval bounds of the registers along a straight-line stretch (for chunked pvm_go proofs).
python3 bounds.py <start> <end>: prints, at each pc, the registers with a known bound (inclusive)."""
import re,sys,os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dis import ins
def p2(b): return (1 << b.bit_length()) - 1
a=int(sys.argv[1]); end=int(sys.argv[2])
B={i:None for i in range(13)}
n=0
while a!=end:
    t,nx=ins[a]
    m=re.match(r'\(\.(\w+) \(\.(\w+)\)(.*)\)',t); kind,op,args=m.group(1),m.group(2),[int(x) for x in m.group(3).split()]
    print(n, a, t, {r:b for r,b in B.items() if b is not None})
    if kind=='twoRegImm':
        d,s,i=args
        if op.startswith('store'): pass
        elif op.startswith('load'): B[d]=None
        elif op in('setLtUImm','setGtUImm','setLtSImm','setGtSImm'): B[d]=1
        elif op=='xorImm': B[d]= max(p2(B[s]),p2(i)) if B[s] is not None else None
        elif op=='andImm': B[d]= i if B[s] is None else min(i,B[s])
        elif op=='addImm64': B[d]= B[s]+i if B[s] is not None and i<2**32 else None
        else: B[d]=None
    elif kind=='threeReg':
        x,y,d=args
        if op in('cmovNz','cmovIz'): B[d]= max(B[x],B[d]) if B[x] is not None and B[d] is not None else None
        elif op in('or','xor'): B[d]= max(p2(B[x]),p2(B[y])) if B[x] is not None and B[y] is not None else None
        elif op=='and': B[d]= min(v for v in (B[x],B[y]) if v is not None) if (B[x] is not None or B[y] is not None) else None
        else: B[d]=None
    elif kind=='twoReg': d,s=args; B[d]=B[s]
    elif kind=='regImm' and op=='loadImm': B[args[0]]=args[1]
    else: B={i:None for i in range(13)}
    a=nx; n+=1
print(n, a, {r:b for r,b in B.items() if b is not None})
