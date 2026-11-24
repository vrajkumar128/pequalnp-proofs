import numpy as np, sys
V=np.load(sys.argv[1])
m=V.shape[0]
M=V.reshape(m,-1)
# row reduce
import scipy.linalg as sl
Q,R,P=sl.qr(M.T,pivoting=True)
# reduced row echelon via pivot columns
A=M.copy()
piv=[]
for r in range(m):
    # choose pivot col with max abs in remaining
    sub=np.abs(A[r:,:])
    i,j=np.unravel_index(np.argmax(sub),sub.shape); i+=r
    A[[r,i]]=A[[i,r]]
    A[r]/=A[r,j]
    for k in range(m):
        if k!=r: A[k]-=A[k,j]*A[r]
    piv.append(j)
np.set_printoptions(precision=4,suppress=True,linewidth=200)
for r in range(m):
    print('pivot',divmod(piv[r],4))
    print(A[r].reshape(4,4))
