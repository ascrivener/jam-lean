import sys; sys.path.insert(0,'.')
from explore import *
import bisect
targets=set(P.jt)
callers={}
for a in sorted(I):
    d=I[a]
    if d and d[0]=='load_imm_jump' and d[1]==0: targets.add(d[3]); callers.setdefault(d[3],[]).append((a,'call'))
    if d and d[0]=='jump': callers.setdefault(d[1],[]).append((a,'jump'))
    if d and d[0]=='load_imm_jump_ind': callers.setdefault(('ind',),[]).append(a)
T=sorted(targets)
def entry(a): return T[bisect.bisect_right(T,a)-1]
def jtidx(t): return [i for i,x in enumerate(P.jt) if x==t]
if __name__=='__main__':
  for a in [33049,50206,58357,58775,6291,7233,7382,7885,8263,11260,14916]:
    e=entry(a)
    print(a,'entry',e,'jt',jtidx(e),'callers',callers.get(e))

retsites=set()
for a in I:
    d=I[a]
    if d and d[0] in('load_imm_jump','load_imm_jump_ind') and d[1]==0:
        retsites.add(P.jt[d[2]//2-1] if d[2]//2-1 < len(P.jt) else None)
T2=sorted({t for t in targets if t not in retsites} | {d[3] for a,d in I.items() if d and d[0]=='load_imm_jump' and d[1]==0})
def entry2(a): return T2[bisect.bisect_right(T2,a)-1]
