import sys; sys.path.insert(0,'.')
from dis import Prog, fmt
P=Prog('/home/user/jam-lean/services/bootstrap/jam-bootstrap-service.jam')
I=P.instrs(); addrs=sorted(I)
# any direct control transfer into wrapper bodies
for a in addrs:
    d=I[a]
    if d and d[0] in ('jump',) : t=d[1]
    elif d and d[0].startswith('branch') or (d and d[0]=='load_imm_jump'): t=d[-1]
    else: continue
    if 40494<=t<=40822 and t not in (40494,40613,40701) and not (40494<=a<=40822):
        print('INTO BODY',a,fmt(d))
def window(a,n=14):
    out=[];i=a
    for _ in range(n):
        out.append(f'  {i}\t{fmt(I[i])}'); i=P.nxt(i)
    return '\n'.join(out)
for tgt in (40494,40701):
  for a in addrs:
    d=I[a]
    if d and d[0]=='load_imm_jump' and d[-1]==tgt:
        r=d[2]; rb=P.jt[r//2-1]
        print(f'CALL {tgt} at {a} ret={r} -> {rb} (next={P.nxt(a)})'); print(window(rb))
    if d and d[0]=='jump' and d[1]==tgt:
        print(f'TAILJUMP {tgt} at {a}')
