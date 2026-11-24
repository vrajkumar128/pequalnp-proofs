import numpy as np, glob, sys, itertools
SOLS='/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231/sols/'
def rank(A,tol=1e-7):
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False); return int((s>tol*max(1,s[0])).sum())
def nullspace(A,tol=1e-7):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1,s[0] if len(s) else 1)).sum()); return vh[r:].conj().T
def ek(t):
    p,q=t.shape; res=[]
    for k in range(1,p+1):
        tot=0
        for R in itertools.combinations(range(p),k):
            for C in itertools.permutations(range(q),k):
                pr=1
                for a,c in zip(R,C): pr*=t[a,c]
                tot+=pr
        res.append(tot)
    return np.array(res)
def P(y):
    mu=lambda a,b:(y[a]*y[b]).sum()
    return mu(0,1)*mu(2,3)+mu(0,2)*mu(1,3)+mu(0,3)*mu(1,2)
rng=np.random.default_rng(0)
for pat in sys.argv[1:]:
  for f in sorted(glob.glob(SOLS+pat+'*.npy'))[:6]:
    V=np.load(f); m,p,q=V.shape
    M=V.reshape(m,-1).T  # (pq, m)
    # row sums map
    Rs=np.array([[V[i,a].sum() for i in range(m)] for a in range(p)])
    r=rank(Rs)
    N0=nullspace(Rs)  # m x k coefficients
    L0=np.einsum('ik,iab->kab',N0,V)
    colr=[rank(V[:,:,j].reshape(m,-1)) for j in range(q)]
    rowr=[rank(V[:,a,:]) for a in range(p)]
    # check level
    c=rng.normal(size=m)+1j*rng.normal(size=m); t=np.einsum('i,iab->ab',c,V)
    lev=np.abs(ek(t)).max()
    # P on L0
    Pv=[]
    for _ in range(3):
        cc=rng.normal(size=L0.shape[0])+1j*rng.normal(size=L0.shape[0]); y=np.einsum('i,iab->ab',cc,L0); Pv.append(abs(P(y)))
    # u_i: row-supported dims
    u=[]
    for a in range(p):
        others=np.concatenate([V[:,b,:] for b in range(p) if b!=a],axis=1)  # m x 3q
        u.append(m-rank(others.T))
    w=[]
    for j in range(q):
        others=V[:,:,[k for k in range(q) if k!=j]].reshape(m,-1)
        w.append(m-rank(others.T))
    print(f.split('/')[-1], 'm',m,'lev %.1e'%lev,'r',r,'dimL0',L0.shape[0],'P(L0) %.2e'%max(Pv),'col',colr,'row',rowr,'u',u,'w',w)
