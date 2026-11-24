import numpy as np, itertools
for (p,q,flags) in [(4,4,''),(4,5,''),(5,5,''),(4,6,''),(4,6,'r'),(4,5,'rc'),(4,4,'rc')]:
    N=p*q
    # S2 as quadratic form: sum over a<b rows, j!=l cols t[a,j] t[b,l]
    Q=np.zeros((N,N))
    for a,b in itertools.combinations(range(p),2):
        for j in range(q):
            for l in range(q):
                if j!=l:
                    Q[a*q+j,b*q+l]+=0.5; Q[b*q+l,a*q+j]+=0.5
    cons=[np.ones(N)]
    if 'r' in flags:
        for i in range(p):
            r=np.zeros((p,q)); r[i]=1; cons.append(r.ravel())
    if 'c' in flags:
        for j in range(q):
            c=np.zeros((p,q)); c[:,j]=1; cons.append(c.ravel())
    A=np.array(cons); u,s,vh=np.linalg.svd(A); rk=np.sum(s>1e-9); K=vh[rk:].T
    Qr=K.T@Q@K
    r=np.linalg.matrix_rank(Qr,1e-9); n=K.shape[1]
    print(p,q,flags,'ambient',n,'rank S2',r,'max isotropic',n-r+r//2)
