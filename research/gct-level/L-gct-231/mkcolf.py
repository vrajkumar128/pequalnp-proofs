import numpy as np, sys, itertools
p,q=4,5
z=np.exp(2j*np.pi/5)
f={k:np.array([z**(k*j) for j in range(q)]) for k in range(1,5)}
P=np.eye(p)-np.ones((p,p))/p; u,s,vh=np.linalg.svd(P); E=vh[:p-1]
for r in [2,3]:
    for ks in itertools.combinations(range(1,5),r):
        out=[np.outer(e,f[k]) for k in ks for e in E]
        name='ambs/4x5cf_%s.npy'%''.join(map(str,ks)); np.save(name,np.array(out)); print(name,len(out))
a=np.array([1,1j,-1,-1j]); c=np.array([1,-1,1,-1]); b=np.array([1,-1j,-1,1j])
P5=np.eye(q)-np.ones((q,q))/q; u,s,vh=np.linalg.svd(P5); E5=vh[:q-1]
for name,vs in [('ac',[a,c]),('cb',[c,b]),('abc_c0',None)]:
    if vs is None: continue
    out=[np.outer(v,e) for v in vs for e in E5]; np.save('ambs/4x5rf_%s.npy'%name,np.array(out)); print(name,len(out))
