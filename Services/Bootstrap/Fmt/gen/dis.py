import re,glob,sys
ins={}
jt={}
for f in glob.glob('Services/Bootstrap/Code*.lean')+glob.glob('Services/Bootstrap/Code*/*.lean'):
    for m in re.finditer(r'\.instr (\d+) (\(.*?\)) (\d+)\]?,?\s*$', open(f).read(), re.M):
        ins[int(m.group(1))]=(m.group(2),int(m.group(3)))
def dump(a,n):
    for _ in range(n):
        if a not in ins: print(a,'??'); return
        i,nx=ins[a]; print(a,i); a=nx
if __name__=='__main__':
    dump(int(sys.argv[1]),int(sys.argv[2]))
