import numpy as np, sys
V=np.load(sys.argv[1]); m=V.shape[0]; shp=V.shape[1:]
A=V.reshape(m,-1).copy()
order=[int(x) for x in sys.argv[2].split(',')] if len(sys.argv)>2 else None
piv=[]
for r in range(m):
    cand=[j for j in (order or range(A.shape[1])) if j not in piv]
    j=max(cand,key=lambda j: np.max(np.abs(A[r:,j]))) if order is None else next(j for j in cand if np.max(np.abs(A[r:,j]))>1e-6)
    i=r+np.argmax(np.abs(A[r:,j]))
    A[[r,i]]=A[[i,r]]; A[r]/=A[r,j]
    for k in range(m):
        if k!=r: A[k]-=A[k,j]*A[r]
    piv.append(j)
np.set_printoptions(precision=4,suppress=True,linewidth=200)
for r in range(m):
    print('pivot',divmod(piv[r],shp[1])); print(A[r].reshape(shp))
