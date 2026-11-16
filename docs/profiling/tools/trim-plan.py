# usage: plan.py cands.tsv [apply]   -- run from the repo root
import re,os,sys,collections
def path(m): return m.replace('.','/')+'.lean'
mods={}
for d in ["PVM","JAM","Services","Tests"]:
    for dp,_,fs in os.walk(d):
        for f in fs:
            if f.endswith('.lean'): mods[os.path.join(dp,f)[:-5].replace('/','.')]=1
for f in ["PVM","JAM","Services"]: mods[f]=1
src={m:open(path(m)).read() for m in mods}
imp0={m:re.findall(r'^import\s+(\S+)',src[m],re.M) for m in mods}
decl=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+([^\s(:{\[]+)',re.M)
names={m:{n.split('.')[-1] for n in decl.findall(src[m])}-{'_',''} for m in mods}
def clo(imp,ms):
    seen=set();st=list(ms)
    while st:
        x=st.pop()
        if x in seen or x not in mods: continue
        seen.add(x); st+=imp.get(x,[])
    return seen
cands=[l.split('\t')[:2] for l in open(sys.argv[1]).read().split('\n') if l and 'RISKY' not in l]
imp={m:list(v) for m,v in imp0.items()}
body={m:re.sub(r'^import.*$','',src[m],flags=re.M) for m in mods}
def uses(m,mod):
    return [n for n in names[mod] if re.search(r'(?<![\w])'+re.escape(n)+r'(?![\w])',body[m])]
def inscope(d):
    return d.startswith('Services.Bootstrap.Alloc.') or d in ('Services.Bootstrap.Reader','Services.Bootstrap.ReaderBig','Services.Bootstrap.Memcpy','Services.Bootstrap.MemcpyBig','Services.Bootstrap.DecodeU16','Services.Bootstrap.DecodeU32','Services.Bootstrap.Decode.Tag')
rev=collections.defaultdict(set)
for m,l in imp0.items():
    for x in l: rev[x].add(m)
def deps(m):
    seen=set();st=[m]
    while st:
        for z in rev.get(st.pop(),()):
            if z not in seen: seen.add(z);st.append(z)
    return seen
changed=set(); skipped=[]
for m,x in cands:
    trial={k:list(v) for k,v in imp.items()}
    rest=[y for y in trial[m] if y!=x]
    c=clo(trial,rest)
    trial[m]=rest+[y for y in imp0[x] if y not in c and y in mods]
    fixes=[]; ok=True
    for d in deps(m)|{m}:
        lost=clo(imp,imp[d])-clo(trial,trial[d])
        for L in sorted(lost):
            if uses(d,L):
                if not inscope(d): ok=False; skipped.append((m,x,d,L)); break
                fixes.append((d,L))
        if not ok: break
    if not ok: continue
    for d,L in fixes:
        if L not in trial[d]: trial[d].append(L)
    imp=trial; changed|={m}|{d for d,_ in fixes}
    print('ACCEPT',m,'-',x,'fixes',fixes)
for s_ in skipped: print('SKIP',*s_)
print('files changed:',len(changed))
if len(sys.argv)>2:
    for m in changed:
        s=src[m]; lines=s.split('\n')
        first=[i for i,l in enumerate(lines) if l.startswith('import ')]
        out=[l for l in lines if not l.startswith('import ')]
        newi=['import '+y for y in imp[m]]
        out[first[0]:first[0]]=newi
        open(path(m),'w').write('\n'.join(out))
