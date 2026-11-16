import sys; sys.path.insert(0,'.')
from explore import *
from funcs import callers, entry2, jtidx
import collections, dis as D
addrs=sorted(I)
idx={a:i for i,a in enumerate(addrs)}
def blockstart(a):
    i=idx[a]
    while i>0 and D.FMT and (I[addrs[i-1]][0] not in [D.NAMES[o] for o in D.TERM]): i-=1
    return addrs[i]
def level(fn, depth=1, seen=()):
    res=[]
    for site,kind in callers.get(fn,[]):
        bs=blockstart(site)
        outs=explore2(bs,fresh(False))
        outs=[o for o in outs if o[2] is not None and o[2].f>0 or o[0]=='pathcap']
        c=collections.Counter(o[0] for o in outs)
        traps=[o[2].n for o in outs if o[0]=='trap']
        # steps after allocfail
        after=[len(o[2].t)-1-o[2].t.index('ALLOCFAIL') for o in outs if o[0]=='trap']
        rets=sorted({o[1] for o in outs if o[0]=='ret'},key=str)
        print('  '*depth+f'caller {site} ({kind}) of {fn} [block {bs}] in fn {entry2(site)}: {dict(c)} trapsAt {sorted({o[1] for o in outs if o[0]=="trap"})} stepsAfterFail max {max(after) if after else None} rets {rets} other {[ (o[0],o[1]) for o in outs if o[0] not in ("trap","ret")][:5]}')
        if rets and depth<4:
            e=entry2(site)
            if e not in seen: level(e,depth+1,seen+(e,))
for fn in (32989,50146,58327,58717):
    print('FN',fn); level(fn)
