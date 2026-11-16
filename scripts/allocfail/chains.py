"""Class (c): follow the Err result from the four returning functions up through their callers.
Runs each caller's call block with an unknown state, models every alloc/realloc call as failing
(w7=0), drops paths that return to the caller without a failure, reports outcomes after failure."""
import sys; sys.path.insert(0,'.')
from explore import *
from funcs import callers
import collections, dis as D
def explore3(pc,st,drop,post=300,maxpaths=200000):
    work=[(st,pc)]; out=[]; seen=set(); n=0
    while work:
        n+=1
        if n>maxpaths: out.append(('pathcap',None,None)); break
        s,p=work.pop()
        if s.f==0 and p in drop: continue
        key=(p,tuple(map(str,s.r)),tuple(sorted(map(str,s.m.items()))),s.d,s.f>0)
        if key in seen: continue
        seen.add(key)
        if s.f==0 and s.n>400: out.append(('prebudget',p,s)); continue
        if s.f>0 and len(s.t)-1-s.t.index('ALLOCFAIL')>post: out.append(('budget',p,s)); continue
        s.n+=1; s.t.append(p)
        res=step(s,p)
        if isinstance(res,tuple): out.append((res[0],res[1],s)); continue
        work.extend(res)
    return out
TN=[D.NAMES[o] for o in D.TERM]
addrs=sorted(I); idx={a:i for i,a in enumerate(addrs)}
def bstart(a):
    i=idx[a]
    while i>0 and I[addrs[i-1]][0] not in TN: i-=1
    return addrs[i]
def retblock(site):
    d=I[site]
    if d[0]=='load_imm_jump': ra=d[2]
    else:
        i=idx[site]
        while not (I[addrs[i]][0]=='load_imm' and I[addrs[i]][1]==0): i-=1
        ra=I[addrs[i]][2]
    return ra,P.jt[ra//2-1]
print('fn\tcaller_site\tkind\tret_addr\tret_block\toutcomes\ttrap_pcs\tmax_steps_after_alloc_fail\tsteps_from_ret_block')
for fn in (32989,50146,50309,58327,58717):
  for site,kind in callers.get(fn,[]):
    ra,rb=retblock(site)
    outs=explore3(bstart(site),fresh(False),drop={rb})
    c=dict(collections.Counter(o[0] for o in outs))
    after=[len(o[2].t)-1-o[2].t.index('ALLOCFAIL') for o in outs if o[0]=='trap']
    fromrb=[len(o[2].t)-o[2].t.index(rb) for o in outs if o[0]=='trap' and rb in o[2].t]
    print(f"{fn}\t{site}\t{kind}\t{ra}\t{rb}\t{c}\t{sorted({o[1] for o in outs if o[0]=='trap'}) or sorted({o[1] for o in outs},key=str)}\t{max(after) if after else '-'}\t{max(fromrb) if fromrb else '-'}")
