import numpy as np, sys
from search2 import *
from scipy.optimize import least_squares
which=sys.argv[1]; trials=int(sys.argv[2]); seed=int(sys.argv[3])
B,amb,m=problem_by_name(which)
rng=np.random.default_rng(seed)
for tr in range(trials):
    pr=Problem(B,amb,m,rng)
    x=rng.normal(size=2*pr.nx)*rng.choice([0.3,1.0,2.0])
    hist=[]
    for rnd in range(6):
        sol=least_squares(pr.res,x,jac=pr.jac,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=2000)
        x=sol.x
        hist.append((normalized_residual(B,pr.V_of(x),rng),sol.nfev,sol.status))
        # random kick small then continue
        x=x+1e-3*rng.normal(size=x.shape)
    print(tr,' '.join('%.2e/%d/%d'%h for h in hist),flush=True)
