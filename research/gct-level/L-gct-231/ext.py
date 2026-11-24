import numpy as np, sys
from search2 import *
from scipy.optimize import least_squares
which=sys.argv[1]; trials=int(sys.argv[2]); seed=int(sys.argv[3])
B, amb, m = problem_by_name(which)
rng=np.random.default_rng(seed)
def ext_dim(V):
    # V: (m,4,4) basis; compute dim of U = {u in amb: <grad perm(B+t), u> = 0 for all t in span V}
    S=200
    C=(rng.normal(size=(S,V.shape[0]))+1j*rng.normal(size=(S,V.shape[0])))
    T=np.einsum('sa,aij->sij',C,V)
    _,G=perm_and_grad(B[None].astype(complex)+T)
    Mx=np.einsum('sij,nij->sn',G,amb)   # S x N
    sv=np.linalg.svd(Mx,compute_uv=False)
    sv=sv/sv[0]
    return amb.shape[0]-np.sum(sv>1e-7), sv
for tr in range(trials):
    pr=Problem(B,amb,m,rng)
    x0=rng.normal(size=2*pr.nx)*rng.choice([0.3,1.0,2.0])
    sol=least_squares(pr.res,x0,jac=pr.jac,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=3000)
    V=pr.V_of(sol.x)
    nr=normalized_residual(B,V,rng)
    if nr<1e-8:
        d,sv=ext_dim(V)
        print(tr,'nr',nr,'nfev',sol.nfev,'extdim',d,'sv tail',np.round(np.log10(sv[-5:]),1),flush=True)
    else:
        print(tr,'nr',nr,'nfev',sol.nfev,flush=True)
