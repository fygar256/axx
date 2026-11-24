import random, sys
random.seed(int(sys.argv[1])); N=int(sys.argv[2])
def run(rules, inp, cap=3000):
    d={(q,s):(w,m,n) for q,s,w,m,n in rules}
    t={i:v for i,v in enumerate(inp)}; q=1; h=0; steps=0
    while q!=0:
        k=(q,t.get(h,0))
        if k not in d: break
        w,m,n=d[k]; t[h]=w; h+= -1 if m==0 else 1; q=n; steps+=1
        if steps>cap: return None
    if not t: return []
    lo,hi=min(t),max(t); cells=[t.get(i,0) for i in range(lo,hi+1)]
    while cells and cells[0]==0: cells.pop(0)
    while cells and cells[-1]==0: cells.pop()
    return cells
src=open('rand.s','w'); exp=bytearray(); cnt=0
while cnt<N:
    ns=random.randint(1,15); sy=random.randint(2,4)
    rules=[]
    for q in range(1,ns+1):
        for s in range(sy):
            if random.random()<0.85:
                rules.append((q,s,random.randrange(sy),random.randrange(2),random.randrange(ns+1)))
    random.shuffle(rules)
    inp=[random.randrange(sy) for _ in range(random.randint(1,8))]
    r=run(rules,inp)
    if r is None: continue
    src.write("TML %s,%s\n"%("+".join(str(v) for ru in rules for v in ru) or "0+0+0+0+0", "+".join(map(str,inp))))
    exp+=bytes([len(r)]+r); cnt+=1
open('rand.exp','wb').write(exp)
