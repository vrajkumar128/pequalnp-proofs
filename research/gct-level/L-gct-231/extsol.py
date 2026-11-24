import os
os.environ['OMP_NUM_THREADS']='1'
import numpy as np, sys, glob
from fast5 import PermPQ, ambient
p,q=int(sys.argv[1]),int(sys.argv[2]); flags=sys.argv[3]; pat=sys.argv[4]
amb=ambient(p,q,'r' in flags,'c' in flags)
pp=PermPQ(p,q); rng=np.random.default_rng(0)
B=np.ones((1,p,q),dtype=complex)
from collections import Counter
cnt=Counter()
for f in sorted(glob.glob(pat))[:40]:
    V=np.load(f); m=V.shape[0]
    C=rng.normal(size=(300,m))+1j*rng.normal(size=(300,m))
    T=np.einsum('sa,aij->sij',C,V)
    P,G=pp.val_grad(B+T)
    Mx=G.reshape(300,-1)@amb.reshape(amb.shape[0],-1).T
    sv=np.linalg.svd(Mx,compute_uv=False); sv/=sv[0]
    ext=amb.shape[0]-np.sum(sv>1e-8)
    cnt[ext]+=1
print('ext dims (m=%d):'%m, dict(cnt))
