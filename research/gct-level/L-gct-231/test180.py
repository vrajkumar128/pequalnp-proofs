import os
os.environ['OMP_NUM_THREADS']='1'
import numpy as np, itertools
from fast5 import PermPQ
w=np.exp(2j*np.pi/3)
rng=np.random.default_rng(0)
pats={'A':np.array([1,w,w**2]),'B':np.array([1,w**2,w])}
def test(q,choice,extra=True):
    pp=PermPQ(4,q); B=np.ones((1,4,q),dtype=complex); P0=pp.val_grad(B)[0][0]
    V=[]
    for k,c in enumerate(choice):
        E=np.zeros((4,q),dtype=complex); E[:3,2*k]=pats[c]; E[:3,2*k+1]=-pats[c]; V.append(E)
    if extra:
        for j in range(q-1):
            E=np.zeros((4,q),dtype=complex); E[3,j]=1; E[3,q-1]=-1; V.append(E)
    V=np.array(V); m=len(V)
    C=rng.normal(size=(300,m))+1j*rng.normal(size=(300,m))
    P,_=pp.val_grad(B+np.einsum('sa,aij->sij',C,V))
    return np.max(np.abs(P-P0))/np.max(np.abs(P))
print('4x5 AB +row3:',test(5,'AB'))
print('4x5 AB only:',test(5,'AB',False))
print('4x6 AB +row3:',test(6,'AB'))
print('4x6 ABA only:',test(6,'ABA',False), 'ABB only', test(6,'ABB',False))
