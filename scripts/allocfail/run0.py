import sys; sys.path.insert(0,'.')
from explore import *
import collections
sites=[]
for a in sorted(I):
    d=I[a]
    if d and d[0]=='load_imm_jump' and d[3] in ALLOC: sites.append((a,d[3],d[2],P.jt[d[2]//2-1]))
for a,t,ra,rb in sites:
    outs=explore(rb,fresh())
    c=collections.Counter(o[0] for o in outs)
    traps=[o[2].n for o in outs if o[0]=='trap']
    print(f'{a} ->{t} ret {ra} blk {rb}: {dict(c)} trap-steps max={max(traps) if traps else None} min={min(traps) if traps else None}',
          ' trapsAt',sorted({o[1] for o in outs if o[0]=='trap'}), ' rets', sorted({o[1] for o in outs if o[0]=='ret'}, key=str))
