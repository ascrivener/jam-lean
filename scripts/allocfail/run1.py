import sys; sys.path.insert(0,'.')
from explore import *
import collections
for a,ra in [(6291,1414),(7233,102),(7382,110),(7885,1576),(8263,1490),(11260,1504),(14916,1046)]:
    rb=P.jt[ra//2-1]
    outs=explore(rb,fresh())
    c=collections.Counter(o[0] for o in outs)
    traps=[o[2].n for o in outs if o[0]=='trap']
    print(f'{a} ->40494 ret {ra} blk {rb}: {dict(c)} steps {traps} trapsAt',sorted({o[1] for o in outs if o[0]=='trap'}),'rets',[o[1] for o in outs if o[0]!='trap'])
    i=rb
    for _ in range(6): print('   ',i,fmt(I[i])); i=P.nxt(i)
