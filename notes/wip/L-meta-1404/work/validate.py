import random, subprocess, itertools
from depthsat import mono_rows
from depthsat2 import depth_sat2
random.seed(7)
def rand_mono(n):
    # random antichain of minterms
    k=random.randint(2,6)
    mins=[]
    for _ in range(k):
        s=random.randint(1,(1<<n)-1)
        mins.append(s)
    f=lambda z: any(all(z[i] for i in range(n) if m>>i&1) for m in mins)
    return f
bad=0
for trial in range(60):
    n=random.choice([4,5,6])
    f=rand_mono(n)
    mins,maxf=mono_rows(n,f)
    if not mins or not maxf: continue
    full=(1<<n)-1
    inst='%d\n%d %s\n%d %s\n'%(n,len(mins),' '.join(map(str,mins)),len(maxf),' '.join(str(full^t) for t in maxf))
    open('v.inst','w').write(inst)
    dk=None
    for k in range(0,10):
        o=subprocess.run(['./kw5',str(k),'1','full'],stdin=open('v.inst'),capture_output=True,text=True).stdout
        if 'FORMULA' in o: dk=k; break
    ds=None
    for k in range(0,10):
        if depth_sat2(n,mins,[t for t in maxf],k): ds=k; break
    if dk!=ds: bad+=1; print('MISMATCH',n,mins,maxf,dk,ds)
print('done, mismatches',bad)
