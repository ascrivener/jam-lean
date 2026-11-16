"""Follow-up: SDK finish_grow (40852) and the other direct callers of picoalloc's core alloc (41177).
Allocators modelled as failing (w7=0 on return): 40494, 40701, 41177 (core alloc_impl),
42980 (core realloc; over-approximates every null it can return). Reaching 41127 (finish_grow's
Err store, shared by the null and the too-large path) also counts as a failure."""
import sys; sys.path.insert(0,'.')
import explore as E
E.ALLOC.update({41177,42980})
from explore import *
from funcs import callers, entry2
import collections, dis as D
_step=E.step
def step2(st,pc):
    if pc==41127 and st.f==0: st.f+=1; st.t.append('ALLOCFAIL')
    return _step(st,pc)
def explore3(pc,st,drop,post=300,maxpaths=300000):
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
        res=step2(s,p)
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
def run(fn,depth=1,seen=()):
  for site,kind in callers.get(fn,[]):
    ra,rb=retblock(site)
    outs=explore3(bstart(site),fresh(False),drop={rb})
    outs=[o for o in outs if o[0]!='prebudget']
    c=dict(collections.Counter(o[0] for o in outs))
    after=[len(o[2].t)-1-o[2].t.index('ALLOCFAIL') for o in outs if o[0]=='trap']
    bad=sorted({(o[0],o[1]) for o in outs if o[0]!='trap'},key=str)
    print(f"{fn}\t{site}\t{kind}\t{ra}\t{rb}\t{entry2(site)}\t{depth}\t{c}\t{sorted({o[1] for o in outs if o[0]=='trap'})}\t{max(after) if after else '-'}\t{bad}",flush=True)
    if any(b[0]=='ret' for b in bad) and depth<5:
        e=entry2(site)
        if e not in seen: run(e,depth+1,seen+(e,))
print('fn\tcaller_site\tkind\tret_addr\tret_block\tcaller_fn\tdepth\toutcomes\ttrap_pcs\tmax_steps_after_fail\tnon_trap')
for fn in [int(x) for x in sys.argv[1:]]: run(fn)
