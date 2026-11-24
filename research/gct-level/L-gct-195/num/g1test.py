import os
os.environ['OMP_NUM_THREADS']='1'; os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np, itertools, sys
from scipy.optimize import least_squares
p=4; q=int(sys.argv[1]); seed=int(sys.argv[2])
rng=np.random.default_rng(seed)
injs={k:[(R,C) for R in itertools.combinations(range(p),k) for C in itertools.permutations(range(q),k)] for k in range(1,5)}
def ek(t,k):
    tot=0
    for R,C in injs[k]:
        pr=1
        for a,c in zip(R,C): pr=pr*t[a,c]
        tot=tot+pr
    return tot
def P(y):
    mu=lambda a,b:(y[a]*y[b]).sum()
    return mu(0,1)*mu(2,3)+mu(0,2)*mu(1,3)+mu(0,3)*mu(1,2)
# sample points for bihomogeneous identities
lams=[np.exp(2j*np.pi*i/6)*1.3**i for i in range(6)]
v=np.array([1,-1,0.5,-0.5])
def unpack(z):
    z=z[:len(z)//2]+1j*z[len(z)//2:]
    y=z[:p*q].reshape(p,q); s=z[p*q:].reshape(p,q); return y,s
def res(z):
    y,s=unpack(z); r=[]
    for k in range(1,5):
        for l in lams[:k+1]:
            r.append(ek(y+l*s,k))
    r+=list(y.sum(axis=1)); r+=list(s.sum(axis=1)-v); r.append(P(y)-1)
    r=np.array(r); return np.concatenate([r.real,r.imag])
best=None
for tr in range(int(sys.argv[3])):
    z0=rng.normal(size=4*p*q)
    sol=least_squares(res,z0,method='trf',max_nfev=3000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    c=np.linalg.norm(sol.fun)
    if best is None or c<best: best=c
    print(tr,'cost %.3e'%c,flush=True)
    if c<1e-10:
        y,s=unpack(sol.x); np.save('g1sol_q%d_%d.npy'%(q,tr),np.stack([y,s])); 
print('best',best)
