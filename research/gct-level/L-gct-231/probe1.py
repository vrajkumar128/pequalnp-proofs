import numpy as np, sys
sys.path.insert(0,'.')
from search import *
rng=np.random.default_rng(3)
B=np.ones((4,4)); amb=sym_basis(); m=3
for tr in range(8):
    amb2,Q,C=setup(B,amb,m,70,rng)
    res,W_of=make_fun(B,amb2,Q,C,m)
    x0=rng.normal(size=2*(9-3)*3)
    for it in range(5):
        sol=least_squares(res,x0,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=4000)
        x0=sol.x
        print(tr,it,np.linalg.norm(sol.fun),np.linalg.norm(sol.x),sol.nfev,sol.status)
