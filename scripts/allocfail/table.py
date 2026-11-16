"""Full table: every call of alloc (40494) / realloc (40701), return block, class, trap pc, steps."""
import sys; sys.path.insert(0,'.')
from explore import *
rows=[]
for a in sorted(I):
    d=I[a]
    if d and d[0]=='load_imm_jump' and d[3] in ALLOC and d[1]==0: rows.append((a,'load_imm_jump',d[3],d[2]))
    if d and d[0]=='jump' and d[1] in ALLOC:
        addrs=sorted(I); i=addrs.index(a)
        while not(I[addrs[i]][0]=='load_imm' and I[addrs[i]][1]==0): i-=1
        rows.append((a,'load_imm ω0;jump',d[1],I[addrs[i]][2]))
print('call_site\tkind\tcallee\tret_addr\treturn_block\tclass\toutcome\ttrap_pc\tsteps_to_trap_or_ret')
for a,k,t,ra in rows:
    rb=P.jt[ra//2-1]
    outs=explore(rb,fresh())
    o=outs[0]; assert len(outs)==1
    cls='a' if o[0]=='trap' else 'c'
    print(f'{a}\t{k}\t{t}\t{ra}\t{rb}\t{cls}\t{o[0]}\t{o[1]}\t{o[2].n}')
