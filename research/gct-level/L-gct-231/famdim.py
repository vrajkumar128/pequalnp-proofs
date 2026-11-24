import numpy as np, sys
from search2 import *
from scipy.optimize import least_squares
which=sys.argv[1]; trials=int(sys.argv[2]); seed=int(sys.argv[3])
B, amb, m = problem_by_name(which)
rng=np.random.default_rng(seed)
for tr in range(trials):
    pr=Problem(B,amb,m,rng)
    x0=rng.normal(size=2*pr.nx)*rng.choice([0.3,1.0,2.0])
    sol=least_squares(pr.res,x0,jac=pr.jac,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=3000)
    V=pr.V_of(sol.x)
    nr=normalized_residual(B,V,rng)
    if nr<1e-8:
        Jr=pr.jac(sol.x)
        sv=np.linalg.svd(Jr,compute_uv=False); sv=sv/sv[0]
        rank_real=np.sum(sv>1e-8)
        print(tr,'nr %.1e'%nr,'nx(complex)',pr.nx,'rank(complex)',rank_real/2,'localdim',pr.nx-rank_real/2,'gap',np.round(np.log10(sv[rank_real-2:rank_real+2]),1),flush=True)
    else:
        print(tr,'nr',nr)
