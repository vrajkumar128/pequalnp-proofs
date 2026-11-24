import numpy as np, sys, itertools
V=np.load(sys.argv[1]); m=V.shape[0]; p,q=V.shape[1:]
M=V.reshape(m,-1)
def rank(A,tol=1e-7):
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False); return int(np.sum(s>tol*max(1,s[0])))
def inter_dim(mask):
    # dim of L ∩ {t supported in mask}
    out=~mask.ravel()
    return m-rank(M[:,out])
print('p,q,m',p,q,m)
for i in range(p):
    mask=np.zeros((p,q),bool); mask[i,:]=True
    print('row',i,'L∩row-supported',inter_dim(mask),'proj rank',rank(M[:,mask.ravel()]))
for j in range(q):
    mask=np.zeros((p,q),bool); mask[:,j]=True
    print('col',j,'L∩col-supported',inter_dim(mask),'proj rank',rank(M[:,mask.ravel()]))
for i,k in itertools.combinations(range(p),2):
    mask=np.zeros((p,q),bool); mask[[i,k],:]=True
    d=inter_dim(mask)
    if d>0: print('rows',i,k,'L∩',d)
for i in range(p):
  for j in range(q):
    mask=np.zeros((p,q),bool); mask[i,:]=True; mask[:,j]=True
    d=inter_dim(mask)
    if d>=m-1: print('row',i,'+col',j,'L∩',d)
