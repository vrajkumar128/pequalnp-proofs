import numpy as np, sys
from search2 import *
from scipy.optimize import least_squares
def zero_sums_basis():
    # 4x4 with zero row and column sums: 9-dim, orthonormal basis
    rows=[]
    for i in range(4):
        r=np.zeros((4,4)); r[i,:]=1; rows.append(r.ravel())
        c=np.zeros((4,4)); c[:,i]=1; rows.append(c.ravel())
    A=np.array(rows)
    u,s,vh=np.linalg.svd(A); rank=np.sum(s>1e-9)
    K=vh[rank:]
    return K.reshape(-1,4,4).astype(complex)
kind=sys.argv[1]; m=int(sys.argv[2]); trials=int(sys.argv[3]); seed=int(sys.argv[4])
B=np.ones((4,4))+np.eye(4)
amb={'sym':sym_basis()/1.0,'zs':zero_sums_basis(),'full':full_basis()}[kind]
if kind=='sym':
    # orthonormalize
    M=amb.reshape(amb.shape[0],-1); q,_=np.linalg.qr(M.T); amb=q.T.reshape(-1,4,4)
rng=np.random.default_rng(seed)
res=run(B,amb,m,trials,seed,verbose=False)
print(kind,m,'best normres',[round(r[0],8) for r in res[:3]])
