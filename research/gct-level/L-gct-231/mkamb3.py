import numpy as np, sys
q=int(sys.argv[1])
# 4 x q matrices with row 0 zero, doubly centered on rows 1..3
out=[]
for i in range(1,4):
    for j in range(q):
        E=np.zeros((4,q)); E[i,j]=1; out.append(E.ravel())
A=np.array(out).T  # 4q x 3q
cons=[]
for i in range(1,4):
    r=np.zeros((4,q)); r[i,:]=1; cons.append(r.ravel())
for j in range(q):
    c=np.zeros((4,q)); c[1:,j]=1; cons.append(c.ravel())
C=np.array(cons)@A
u,s,vh=np.linalg.svd(C); rk=np.sum(s>1e-9); K=vh[rk:].T
B=(A@K).T.reshape(-1,4,q)
np.save('amb_%d_rows123.npy'%q,B); print(B.shape)
