import re,sys
src,dst=sys.argv[1],sys.argv[2]
L=open(src).read().split('\n'); out=[]
decl=re.compile(r'^(@\[[^\]]*\]\s*)?((private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive)\s+(\S+)')
for l in L:
    m=decl.match(l)
    if m:
        j=len(out)
        while j>0 and out[j-1].strip()!='': j-=1
        out.insert(j,f'#eval show IO Unit from do IO.eprintln s!"@T {{← IO.monoMsNow}} {m.group(5)}"')
    out.append(l)
out.append('#eval show IO Unit from do IO.eprintln s!"@T {← IO.monoMsNow} END"')
open(dst,'w').write('\n'.join(out))
