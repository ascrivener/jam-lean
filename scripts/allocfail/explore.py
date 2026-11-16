"""Abstract path explorer: from a state where an allocator just returned null (w7=0),
follow every path (forking on undecided branches) until trap / return-to-unknown / budget."""
import sys; sys.path.insert(0,'.')
from dis import Prog, fmt
P=Prog('/home/user/jam-lean/services/bootstrap/jam-bootstrap-service.jam')
I=P.instrs()
M=(1<<64)-1
ALLOC={40494,40701}
def s64(x): return x-(1<<64) if x>>63 else x
def s32(x): x&=0xffffffff; return x-(1<<32) if x>>31 else x
class St:
    def __init__(s,regs,mem,depth,steps,trace,flag):
        s.r=regs; s.m=mem; s.d=depth; s.n=steps; s.t=trace; s.f=flag
    def cp(s): return St(list(s.r),dict(s.m),s.d,s.n,list(s.t),s.f)
def isc(v): return isinstance(v,int)
def addv(v,k):
    if isc(v): return (v+k)&M
    if isinstance(v,tuple): return (v[0],(v[1]+k)&M)
    return None
def ld(st,addr,w,signed=False):
    if isinstance(addr,tuple) and addr[0]=='sp':
        v=st.m.get((s64(addr[1]),w))
        if isc(v) and signed: 
            b=8*w; v&=(1<<b)-1
            if v>>(b-1): v=(v-(1<<b))&M
        return v
    return None
def stv(st,addr,w,v):
    if isinstance(addr,tuple) and addr[0]=='sp':
        o=s64(addr[1])
        for k in list(st.m):
            if k[0]<o+w and o<k[0]+k[1]: del st.m[k]
        if isc(v) and w<8: v&=(1<<(8*w))-1
        st.m[(o,w)]=v
    # stores through unknown pointers: assume they don't alias the tracked stack (study approximation)
def cmp(op,a,b):
    if not(isc(a) and isc(b)):
        if isinstance(a,tuple) and isinstance(b,tuple) and a[0]==b[0]: a,b=a[1],b[1]
        else: return None
    if op=='eq': return a==b
    if op=='ne': return a!=b
    if op=='lt_u': return a<b
    if op=='le_u': return a<=b
    if op=='ge_u': return a>=b
    if op=='gt_u': return a>b
    if op=='lt_s': return s64(a)<s64(b)
    if op=='le_s': return s64(a)<=s64(b)
    if op=='ge_s': return s64(a)>=s64(b)
    if op=='gt_s': return s64(a)>s64(b)
WID={'u8':1,'i8':1,'u16':2,'i16':2,'u32':4,'i32':4,'u64':8}
def step(st,pc):
    """returns list of (state,nextpc) or terminal ('trap'|'ret'|'ind'|...,detail)."""
    d=I.get(pc)
    if d is None: return ('badpc',pc)
    op=d[0]; r=st.r; nx=P.nxt(pc)
    U=lambda x: x
    if op=='trap': return ('trap',pc)
    if op in('fallthrough','unlikely'): return [(st,nx)]
    if op=='ecalli': r[7]=None; r[8]=None; return [(st,nx)]
    if op=='jump':
        t=d[1]
        if t in ALLOC: return alloc_ret(st, r[0], tail=True)
        return [(st,t)]
    if op=='load_imm_jump':
        a,x,t=d[1],d[2],d[3]; r[a]=x
        if t in ALLOC and a==0:
            return alloc_ret(st,x,tail=False)
        if a==0: st.d+=1
        return [(st,t)]
    if op=='jump_ind':
        a,x=d[1],d[2]; v=addv(r[a],x)
        if a==0 and x==0 and v is None and st.d==0: return ('ret',pc)
        if isc(v):
            if a==0: st.d-=1
            k=v//2-1
            if v%2==0 and 0<=k<len(P.jt): return [(st,P.jt[k])]
            return ('badjump',pc)
        return ('ind',pc)
    if op=='load_imm_jump_ind':
        a,b,x,y=d[1:]; v=addv(r[b],y); r[a]=x
        if a==0: st.d+=1
        if isc(v):
            k=v//2-1
            if v%2==0 and 0<=k<len(P.jt): return [(st,P.jt[k])]
        return ('ind',pc)
    if op=='load_imm': r[d[1]]=d[2]; return [(st,nx)]
    if op=='load_imm_64': r[d[1]]=d[2]; return [(st,nx)]
    if op=='move_reg': r[d[1]]=r[d[2]]; return [(st,nx)]
    if op.startswith('branch_'):
        c=op[7:]
        if c.endswith('_imm'):
            c=c[:-4]; a,x,t=d[1],d[2],d[3]; res=cmp(c,r[a],x)
        else:
            a,b,t=d[1],d[2],d[3]; res=cmp(c,r[a],r[b])
        if res is None:
            s2=st.cp(); return [(st,t),(s2,nx)]
        return [(st,t if res else nx)]
    if op.startswith('store_imm_ind_'):
        a,x,y=d[1],d[2],d[3]; stv(st,addv(r[a],x),WID[op.split('_')[-1]],y); return [(st,nx)]
    if op.startswith('store_ind_'):
        a,b,x=d[1],d[2],d[3]; stv(st,addv(r[b],x),WID[op.split('_')[-1]],r[a]); return [(st,nx)]
    if op.startswith('load_ind_'):
        a,b,x=d[1],d[2],d[3]; w=op.split('_')[-1]; r[a]=ld(st,addv(r[b],x),WID[w],w[0]=='i'); return [(st,nx)]
    if op.startswith('store_imm_u') or op.startswith('store_u'): return [(st,nx)]
    if op.startswith('load_u') or op.startswith('load_i'): r[d[1]]=None; return [(st,nx)]
    if FMT_of(op)=='twoRegImm':
        a,b,x=d[1],d[2],d[3]; v=r[b]
        if op=='add_imm_64': r[a]=addv(v,x)
        elif op=='add_imm_32': r[a]=(s32(v+x))&M if isc(v) else None
        elif isc(v):
            f={'and_imm':lambda:v&x,'or_imm':lambda:v|x,'xor_imm':lambda:v^x,
               'shlo_r_imm_64':lambda:v>>(x%64),'shlo_l_imm_64':lambda:(v<<(x%64))&M,
               'shar_r_imm_64':lambda:(s64(v)>>(x%64))&M,'mul_imm_64':lambda:(v*x)&M,
               'set_lt_u_imm':lambda:int(v<x),'set_gt_u_imm':lambda:int(v>x),
               'set_lt_s_imm':lambda:int(s64(v)<s64(x)),'set_gt_s_imm':lambda:int(s64(v)>s64(x)),
               'neg_add_imm_64':lambda:(x-v)&M}.get(op)
            r[a]=f() if f else None
            if op in('cmov_iz_imm','cmov_nz_imm'):
                r[a]=x if ((v==0)==(op=='cmov_iz_imm')) else st.r[a]
        else:
            if op=='cmov_iz_imm' or op=='cmov_nz_imm': r[a]=None
            else: r[a]=None
        return [(st,nx)]
    if FMT_of(op)=='threeReg':
        a,b,dd=d[1],d[2],d[3]; va,vb=r[a],r[b]
        if op=='cmov_iz':
            r[dd]= va if (isc(vb) and vb==0) else (r[dd] if isc(vb) else None)
        elif op=='cmov_nz':
            r[dd]= va if (isc(vb) and vb!=0) else (r[dd] if isc(vb) else None)
        elif op=='add_64':
            if isc(va) and isc(vb): r[dd]=(va+vb)&M
            elif isinstance(va,tuple) and isc(vb): r[dd]=addv(va,vb)
            elif isinstance(vb,tuple) and isc(va): r[dd]=addv(vb,va)
            else: r[dd]=None
        elif isc(va) and isc(vb):
            f={'sub_64':lambda:(va-vb)&M,'and':lambda:va&vb,'or':lambda:va|vb,'xor':lambda:va^vb,
               'set_lt_u':lambda:int(va<vb),'mul_64':lambda:(va*vb)&M}.get(op)
            r[dd]=f() if f else None
        else: r[dd]=None
        return [(st,nx)]
    # everything else: clobber destination conservatively
    if FMT_of(op)=='twoReg': r[d[1]]=None
    elif FMT_of(op)=='regExtImm': r[d[1]]=d[2]
    return [(st,nx)]
from dis import FMT
OPN={}
import dis as D
for k,v in D.NAMES.items(): OPN[v]=FMT[k]
def FMT_of(op): return OPN[op]
def alloc_ret(st,ra,tail):
    """Model a failing allocator call: returns to ra with w7=0, temporaries clobbered."""
    st.f+=1
    for k in (2,3,4,8,9,10,11,12): st.r[k]=None
    st.r[7]=0
    st.t.append('ALLOCFAIL')
    if tail:
        if ra is None and st.d==0: return ('ret',None)  # tail call from start fn: null returned to caller
        if ra is None: return ('ind',None)
        st.d-=1
    k=ra//2-1
    return [(st,P.jt[k])]
def explore(pc,st,maxsteps=400,maxpaths=4000,need_flag=False):
    work=[(st,pc)]; out=[]
    while work:
        if len(out)+len(work)>maxpaths: out.append(('pathcap',None,None)); break
        s,p=work.pop()
        if s.n>maxsteps: out.append(('budget',p,s)); continue
        s.n+=1; s.t.append(p)
        res=step(s,p)
        if isinstance(res,tuple): out.append((res[0],res[1],s)); continue
        work.extend(res)
    return out
def fresh(w7null=True):
    r=[None]*13; r[1]=('sp',0)
    if w7null: r[7]=0
    return St(r,{},0,0,[],1 if w7null else 0)

def explore2(pc,st,pre=400,post=300,maxpaths=200000):
    """Like explore, but the post-failure step budget is counted from the failing allocator call,
    paths that never fail within `pre` steps are dropped, and identical (pc,state) pairs are merged."""
    work=[(st,pc)]; out=[]; seen=set(); n=0
    while work:
        n+=1
        if n>maxpaths: out.append(('pathcap',None,None)); break
        s,p=work.pop()
        key=(p,tuple(map(str,s.r)),tuple(sorted(map(str,s.m.items()))),s.d,s.f>0)
        if key in seen: continue
        seen.add(key)
        if s.f==0 and s.n>pre: continue
        if s.f>0:
            k=len(s.t)-1-s.t.index('ALLOCFAIL')
            if k>post: out.append(('budget',p,s)); continue
        s.n+=1; s.t.append(p)
        res=step(s,p)
        if isinstance(res,tuple):
            if s.f>0: out.append((res[0],res[1],s))
            continue
        work.extend(res)
    return out
