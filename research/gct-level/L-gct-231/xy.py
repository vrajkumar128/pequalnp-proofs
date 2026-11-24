import numpy as np
from search2 import perm_and_grad
from scipy.optimize import least_squares
rng=np.random.default_rng(0)
C=(rng.normal(size=(80,3))+1j*rng.normal(size=(80,3)))
def unpack(p):
    z=p[:len(p)//2]+1j*p[len(p)//2:]
    x=z[:4]; X=z[4:7].reshape(1,3)
    W=np.vstack([np.eye(3),X])  # 4x3, y-basis columns
    return x,W
def res(p):
    x,W=unpack(p)
    Y=C@W.T  # samples x 4
    T=x[None,:,None]*Y[:,None,:]+Y[:,:,None]*x[None,None,:]
    P,_=perm_and_grad(np.ones((1,4,4))+T)
    f=P-24
    return np.concatenate([f.real,f.imag])
best=9
for tr in range(0):
    p0=rng.normal(size=14)
    s=least_squares(res,p0,method='lm',max_nfev=3000)
    r=np.linalg.norm(s.fun)
    if r<best: best=r; print(tr,r,flush=True)
print('best',best)
for tr in range(20):
    p0=rng.normal(size=14)
    s=least_squares(res,p0,method='lm',max_nfev=3000)
    x,W=unpack(s.x)
    print(np.linalg.norm(s.fun), np.round(x,4), np.linalg.norm(W))
