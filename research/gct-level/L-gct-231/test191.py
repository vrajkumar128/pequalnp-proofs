import os
os.environ['OMP_NUM_THREADS']='1'
import numpy as np, itertools
from fast5 import PermPQ
w=np.exp(2j*np.pi/3)
pp=PermPQ(4,6); rng=np.random.default_rng(0)
B=np.ones((1,4,6),dtype=complex); P0=pp.val_grad(B)[0][0]
pats={'A':np.array([1,w,w**2]),'B':np.array([1,w**2,w])}
for choice in itertools.product('AB',repeat=3):
    V=[]
    for k,c in enumerate(choice):
        E=np.zeros((4,6),dtype=complex); E[:3,2*k]=pats[c]; E[:3,2*k+1]=-pats[c]; V.append(E)
    for j in range(5):
        E=np.zeros((4,6),dtype=complex); E[3,j]=1; E[3,5]=-1; V.append(E)
    V=np.array(V); m=len(V)
    C=rng.normal(size=(300,m))+1j*rng.normal(size=(300,m))
    P,_=pp.val_grad(B+np.einsum('sa,aij->sij',C,V))
    print(choice,'dim',np.linalg.matrix_rank(V.reshape(m,-1)),'max|perm-360|/max|perm|=%.2e'%(np.max(np.abs(P-P0))/np.max(np.abs(P))))
