import numpy as np
from search2 import perm_and_grad
from scipy.optimize import least_squares
rng=np.random.default_rng(1)
C=(rng.normal(size=(80,3))+1j*rng.normal(size=(80,3)))
Q,_=np.linalg.qr(rng.normal(size=(4,4))+1j*rng.normal(size=(4,4)))
Q2,_=np.linalg.qr(rng.normal(size=(4,4))+1j*rng.normal(size=(4,4)))
def unpack(p):
    z=p[:len(p)//2]+1j*p[len(p)//2:]
    x=Q@np.concatenate([[1],z[:3]]); X=z[3:6].reshape(1,3)
    W=Q2@np.vstack([np.eye(3),X])
    return x,W
def res(p):
    x,W=unpack(p)
    Y=C@W.T
    T=x[None,:,None]*Y[:,None,:]+Y[:,:,None]*x[None,None,:]
    P,_=perm_and_grad(np.ones((1,4,4))+T)
    f=P-24
    return np.concatenate([f.real,f.imag])
best=9
for tr in range(300):
    p0=rng.normal(size=12)
    s=least_squares(res,p0,method='lm',max_nfev=3000)
    r=np.linalg.norm(s.fun)
    if r<best: best=r; print(tr,r,np.round(unpack(s.x)[0],4),flush=True)
print('best',best)
