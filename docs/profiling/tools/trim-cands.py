import re,os,sys,glob
def path(m): return m.replace('.','/')+'.lean'
def imps(m):
    return re.findall(r'^import\s+(\S+)',open(path(m)).read(),re.M)
decl=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|irreducible_def)\s+([^\s(:{\[]+)',re.M)
risky=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(instance|notation|infix|prefix|macro|syntax|elab|simproc|dsimproc|register_simp_attr|attribute|scoped|local notation|declare)',re.M)
targets=[p for p in glob.glob('Services/Bootstrap/Alloc/*.lean')]+['Services/Bootstrap/'+f for f in ['Reader.lean','ReaderBig.lean','Memcpy.lean','MemcpyBig.lean','DecodeU16.lean','DecodeU32.lean','Decode/Tag.lean']]
for t in sorted(targets):
    m=t[:-5].replace('/','.')
    src=open(t).read()
    body=re.sub(r'^import.*$','',src,flags=re.M)
    for x in imps(m):
        if not os.path.exists(path(x)): continue
        xs=open(path(x)).read()
        names={n.split('.')[-1] for _,n in decl.findall(xs)}
        names={n for n in names if n and n!='_'}
        used=[n for n in names if re.search(r'(?<![\w.])'+re.escape(n)+r'(?![\w])',body) or re.search(r'\.'+re.escape(n)+r'(?![\w])',body)]
        if not used:
            print(f"{m}\t{x}\t{'RISKY' if (risky.search(xs) or not names) else ''}")
