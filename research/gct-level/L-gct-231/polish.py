import numpy as np, sys
from search2 import *
from scipy.optimize import least_squares, minimize
which=sys.argv[1]; trials=int(sys.argv[2]); seed=int(sys.argv[3])
B,amb,m=problem_by_name(which)
rng=np.random.default_rng(seed)
for tr in range(trials):
    pr=Problem(B,amb,m,rng)
    x=rng.normal(size=2*pr.nx)*rng.choice([0.3,1.0,2.0])
    sol=least_squares(pr.res,x,jac=pr.jac,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=2000)
    x=sol.x
    phi=lambda x: 0.5*np.sum(pr.res(x)**2)
    grad=lambda x: pr.jac(x).T@pr.res(x)
    out=['LM %.2e'%np.linalg.norm(sol.fun)]
    for rnd in range(4):
        r=minimize(phi,x,jac=grad,method='BFGS',options={'gtol':1e-30,'maxiter':5000})
        x=r.x
        out.append('%.2e'%np.sqrt(2*r.fun))
    print(tr,' '.join(out),flush=True)
