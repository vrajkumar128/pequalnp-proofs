import os
os.environ['OMP_NUM_THREADS']='1'
import numpy as np, sys, glob
from fast5 import PermPQ, ambient
p,q=int(sys.argv[1]),int(sys.argv[2]); flags=sys.argv[3]; pat=sys.argv[4]
amb=ambient(p,q,'r' in flags,'c' in flags); A2=amb.reshape(amb.shape[0],-1)
pp=PermPQ(p,q); rng=np.random.default_rng(0)
B=np.ones((1,p,q),dtype=complex); P0=pp.val_grad(B)[0][0]
for f in sorted(glob.glob(pat))[:15]:
    V=np.load(f); m=V.shape[0]
    C=rng.normal(size=(400,m))+1j*rng.normal(size=(400,m))
    T=np.einsum('sa,aij->sij',C,V)
    P,G=pp.val_grad(B+T)
    Mx=G.reshape(400,-1)@A2.T
    u,s,vh=np.linalg.svd(Mx); s/=s[0]; ns=vh[np.sum(s>1e-8):].conj()
    U=ns@A2   # ext vectors (flattened)
    Vm=V.reshape(m,-1).T
    proj=U.T-Vm@np.linalg.lstsq(Vm,U.T,rcond=None)[0]
    # basis of complement directions
    uu,ss,_=np.linalg.svd(proj,full_matrices=False); k=ns.shape[0]-m
    errs=[]
    for d in range(k):
        W=np.concatenate([V,uu[:,d].reshape(1,p,q)])
        C2=rng.normal(size=(400,m+1))+1j*rng.normal(size=(400,m+1))
        P2,_=pp.val_grad(B+np.einsum('sa,aij->sij',C2,W))
        errs.append(np.max(np.abs(P2-P0))/np.max(np.abs(P2)))
    print(f.split('/')[-1],'extra dirs',k,'rel level err of span(L,u):',['%.1e'%e for e in errs])
