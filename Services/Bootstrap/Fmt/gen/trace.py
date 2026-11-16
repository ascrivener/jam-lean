import re,sys
sys.path.insert(0,'/tmp/claude-0/sp')
from dis import ins
a=int(sys.argv[1]); end=int(sys.argv[2])
R={i:f'r{i}' for i in range(13)}
M={}
while a!=end:
    t,nx=ins[a]
    m=re.match(r'\(\.(\w+) \(\.(\w+)\)(.*)\)',t); kind,op,args=m.group(1),m.group(2),m.group(3).split()
    args=[int(x) for x in args]
    if kind=='twoRegImm':
        d,s,i=args
        if op.startswith('store'): M[i]=R[d] if False else R[d]; M[('st',i)]=R[d]
        elif op.startswith('load'): R[d]=M.get(('st',i),f'[r{s}+{i}]') if s==1 else f'ld{op[-2:]}(r{s}0+{i})'
        else: R[d]=f'{op}({R[s]},{i})'
    elif kind=='threeReg':
        x,y,d=args
        if op=='cmovNz': R[d]=f'({R[y]}!=0?{R[x]}:{R[d]})'
        elif op=='cmovIz': R[d]=f'({R[y]}==0?{R[x]}:{R[d]})'
        else: R[d]=f'{op}({R[x]},{R[y]})'
    elif kind=='twoReg':
        d,s=args; R[d]=R[s]
    elif kind=='regImm' and op=='loadImm':
        R[args[0]]=str(args[1])
    a=nx
for i in [5,7,8,9,12]: print(i, R[i][:300], len(R[i]))
