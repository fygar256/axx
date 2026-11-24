import random, subprocess, sys
imp=sys.argv[1:]; random.seed(3)
rules=[1,1,1,1,1,1,2,2,1,1,1,0,0,0,2,2,2,1,0,2,2,1,2,0,0,2,0,2,0,0]
def run(inp):
    d={(rules[i],rules[i+1]):tuple(rules[i+2:i+5]) for i in range(0,len(rules),5)}
    t={i:v for i,v in enumerate(inp)}; q=1;h=0
    while q:
        k=(q,t.get(h,0))
        if k not in d: break
        w,m,n=d[k]; t[h]=w; h+=-1 if m==0 else 1; q=n
    c=[t.get(i,0) for i in range(min(t,default=0),max(t,default=0)+1)]
    while c and c[0]==0: c.pop(0)
    while c and c[-1]==0: c.pop()
    return c
ok=0;N=int(imp.pop(0))
for _ in range(N):
    w=[random.randrange(3) for _ in range(random.randint(0,9))]
    open('r4.s','w').write(''.join('D %d\n'%v for v in w)+'END\n')
    subprocess.run(imp+['inc_file.axx','r4.s','-b','r4.bin'],capture_output=True)
    d=open('r4.bin','rb').read(); i=d.index(255)
    pad=0
    for v in w: pad=pad*3+v+1
    good = i==pad and set(d[:i])<= {0} and list(d[i+1:])==run(w)
    ok+=good
    if not good: print('FAIL',w)
print(ok,'/',N)
