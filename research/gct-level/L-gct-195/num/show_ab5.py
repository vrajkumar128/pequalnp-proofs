import numpy as np
np.set_printoptions(precision=3, suppress=True, linewidth=150)
SOLS='/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231/sols/'
V=np.load(SOLS+'F_ab5_t2.npy'); m,p,q=V.shape
M=V.reshape(m,-1)
# reduced row echelon on columns ordered: rows 0..2 first then row 3
def rref(A,tol=1e-8):
    A=A.copy(); r=0; piv=[]
    for c in range(A.shape[1]):
        if r>=A.shape[0]: break
        i=np.argmax(np.abs(A[r:,c]))+r
        if abs(A[i,c])<tol: continue
        A[[r,i]]=A[[i,r]]; A[r]/=A[r,c]
        for k in range(A.shape[0]):
            if k!=r: A[k]-=A[k,c]*A[r]
        piv.append(c); r+=1
    return A[:r],piv
R,piv=rref(M)
for i in range(R.shape[0]):
    print(np.round(R[i].reshape(p,q),3)); print()
