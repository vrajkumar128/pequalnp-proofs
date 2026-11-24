import os
os.environ['OMP_NUM_THREADS']='1'
import numpy as np, sys
from fast5 import PermPQ
F=np.load(sys.argv[1]); p,q=F.shape[1:]
pp=PermPQ(p,q); rng=np.random.default_rng(0); B=np.ones((1,p,q),dtype=complex); P0=pp.val_grad(B)[0][0]
m=F.shape[0]; C=rng.normal(size=(300,m))+1j*rng.normal(size=(300,m))
P,_=pp.val_grad(B+np.einsum('sa,aij->sij',C,F))
print('dim',np.linalg.matrix_rank(F.reshape(m,-1)),'rel err %.2e'%(np.max(np.abs(P-P0))/np.max(np.abs(P))))
