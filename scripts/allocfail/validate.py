import re,sys,glob
sys.path.insert(0,'.')
from dis import Prog
P=Prog('/home/user/jam-lean/services/bootstrap/jam-bootstrap-service.jam')
pat=re.compile(r'theorem d_(\d+) .*?P\.decode \d+ = some \(\.(\w+) \(\.(\w+)\)((?: -?\d+)*)\) ∧ P\.next \d+ = (\d+)')
pat2=re.compile(r'theorem d_(\d+) .*?P\.decode \d+ = some \(\.(\w+) \(\.(\w+)\)\) ∧ P\.next \d+ = (\d+)')
n=bad=0
files=glob.glob('/home/user/jam-lean/Services/Bootstrap/Code*.lean')+glob.glob('/home/user/jam-lean/Services/Bootstrap/Code*/*.lean')
seen=set()
for f in files:
  for line in open(f):
    if 'theorem d_' not in line: continue
    m=pat.search(line); args=None
    if m: a,_,op,args,nx=m.groups(); args=[int(x) for x in args.split()]
    else:
      m=pat2.search(line)
      if not m: continue
      a,_,op,nx=m.groups(); args=[]
    a=int(a); nx=int(nx)
    if a in seen: continue
    seen.add(a); n+=1
    d=P.decode(a)
    mine=[x if x>=0 else x for x in d[1:]]
    ok = d[0].replace('_','').lower()==op.lower() and mine==args and P.nxt(a)==nx
    if not ok:
      bad+=1
      if bad<10: print('MISMATCH',a,op,args,nx,'vs',d,P.nxt(a))
print('checked',n,'mismatch',bad)
