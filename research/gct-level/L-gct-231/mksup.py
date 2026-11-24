import numpy as np, sys
# usage: mksup.py p q R C flags out   (R, C: comma lists of row / column indices whose full lines are in the support; flags: r = zero row sums, c = zero col sums)
p,q=int(sys.argv[1]),int(sys.argv[2])
R=[int(x) for x in sys.argv[3].split(',') if x!='']
C=[int(x) for x in sys.argv[4].split(',') if x!='']
flags=sys.argv[5]; out=sys.argv[6]
sup=[(i,j) for i in range(p) for j in range(q) if i in R or j in C]
A=[]
for (i,j) in sup:
    E=np.zeros((p,q)); E[i,j]=1; A.append(E.ravel())
A=np.array(A).T
cons=[]
if 'r' in flags:
    for i in range(p):
        r=np.zeros((p,q)); r[i,:]=1; cons.append(r.ravel())
if 'c' in flags:
    for j in range(q):
        c=np.zeros((p,q)); c[:,j]=1; cons.append(c.ravel())
if cons:
    Cm=np.array(cons)@A
    u,s,vh=np.linalg.svd(Cm); rk=int(np.sum(s>1e-9)); K=vh[rk:].T
    A=A@K
np.save(out,A.T.reshape(-1,p,q)); print(out,A.shape[1])
