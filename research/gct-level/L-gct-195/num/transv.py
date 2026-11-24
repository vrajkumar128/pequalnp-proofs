import numpy as np, glob, sys, itertools
SOLS='/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231/sols/'
def rank(A,tol=1e-7):
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False); return int((s>tol*max(1,s[0])).sum())
for pat in sys.argv[1:]:
  for f in sorted(glob.glob(SOLS+pat+'*.npy'))[:4]:
    V=np.load(f); m,p,q=V.shape
    rho=np.array([[V[i,a].sum() for i in range(m)] for a in range(p)])
    r=rank(rho)
    best=99; bestT=None
    for T in itertools.product(range(p),repeat=q):
        F=np.vstack([rho]+[V[:,T[j],j][None,:] for j in range(q)])
        k=rank(F)
        if k<best: best=k; bestT=T
    print(f.split('/')[-1],'m',m,'r',r,'min rank(rho+transversal)',best,bestT, ' => W dim',m-best)
