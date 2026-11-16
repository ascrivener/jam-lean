# sim.py ROOT times.tsv [cores]  -- critical path (infinite cores) and list-scheduling makespan
import os,re,sys,heapq,statistics
root,tsv=sys.argv[1],sys.argv[2]; cores=int(sys.argv[3]) if len(sys.argv)>3 else 4
os.chdir(root)
mods={}
for d in ["PVM","JAM","Services"]:
    for dp,_,fs in os.walk(d):
        for f in fs:
            if f.endswith('.lean'): mods[os.path.join(dp,f)[:-5].replace('/','.')]=os.path.join(dp,f)
for f in ["PVM","JAM","Services"]: mods[f]=f+'.lean'
imp={m:[x for x in re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(\S+)',open(p).read(),re.M) if x in mods] for m,p in mods.items()}
t={}
for l in open(tsv):
    if l.startswith('#') or not l.strip(): continue
    a=l.split('\t'); t[a[0]]=float(a[1])
known=[t[m] for m in mods if m in t]
# impute missing by size ratio (sec per byte, median)
rate=statistics.median([t[m]/max(1,os.path.getsize(mods[m])) for m in mods if m in t])
w={m:t.get(m, rate*os.path.getsize(mods[m])) for m in mods}
miss=sum(1 for m in mods if m not in t)
import json
for m,k in json.loads(os.environ.get('SPLIT','{}')).items():
    if m in w: w[m]=w[m]*k+5   # k = fraction of the file in its largest shard (slowest theorem)

ch=os.environ.get('CHANGED')
if ch:
    rv={}
    for m in mods:
        for y in imp[m]: rv.setdefault(y,[]).append(m)
    aff={ch}; st=[ch]
    while st:
        for z in rv.get(st.pop(),[]):
            if z not in aff: aff.add(z); st.append(z)
    w={m:(w[m] if m in aff else 0.0) for m in mods}
    print('affected',len(aff))
memo={}
order=[]; seen=set()
def topo(m):
    st=[(m,0)]
    while st:
        x,i=st.pop()
        if i==0:
            if x in seen: continue
            seen.add(x); st.append((x,1)); st+= [(y,0) for y in imp[x] if y not in seen]
        else: order.append(x)
for m in mods: topo(m)
fin={}; pred={}
for m in order:
    b=max(imp[m],key=lambda y:fin[y],default=None)
    fin[m]=w[m]+(fin[b] if b else 0); pred[m]=b
end=max(fin,key=fin.get)
chain=[];x=end
while x: chain.append(x); x=pred[x]
chain.reverse()
print(f"modules {len(mods)} (imputed {miss}), total {sum(w.values())/60:.0f} min, critical path {fin[end]/60:.1f} min, {len(chain)} modules")
for m in sorted(chain,key=lambda m:-w[m])[:12]: print(f"  {w[m]:6.0f}s {m}")
# list scheduling, priority = longest remaining path (bottom level)
rev={m:[] for m in mods}
for m in mods:
    for y in imp[m]: rev[y].append(m)
bl={}
for m in reversed(order): bl[m]=w[m]+max((bl[z] for z in rev[m]),default=0)
indeg={m:len(set(imp[m])) for m in mods}
ready=[(-bl[m],m) for m in mods if indeg[m]==0]; heapq.heapify(ready)
running=[]; now=0.0; done=0
while ready or running:
    while ready and len(running)<cores:
        _,m=heapq.heappop(ready); heapq.heappush(running,(now+w[m],m))
    now,m=heapq.heappop(running); done+=1
    for z in set(rev[m]):
        indeg[z]-=1
        if indeg[z]==0: heapq.heappush(ready,(-bl[z],z))
print(f"{cores}-core makespan {now/60:.0f} min")
