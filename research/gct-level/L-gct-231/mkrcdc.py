import numpy as np, sys
# ambient: full rows R and full cols C, plus doubly centered block on the remaining rows x remaining cols
p,q=int(sys.argv[1]),int(sys.argv[2])
R=[int(x) for x in sys.argv[3].split(',') if x!='']
C=[int(x) for x in sys.argv[4].split(',') if x!='']
out=sys.argv[5]
vecs=[]
for i in range(p):
    for j in range(q):
        if i in R or j in C:
            E=np.zeros((p,q)); E[i,j]=1; vecs.append(E.ravel())
rr=[i for i in range(p) if i not in R]; cc=[j for j in range(q) if j not in C]
# doubly centered on rr x cc
blk=[]
for i in rr:
    for j in cc:
        E=np.zeros((p,q)); E[i,j]=1; blk.append(E.ravel())
A=np.array(blk).T
cons=[]
for i in rr:
    r=np.zeros((p,q)); r[i,cc]=1; cons.append(r.ravel())
for j in cc:
    c=np.zeros((p,q)); c[rr,j]=1; cons.append(c.ravel())
Cm=np.array(cons)@A
u,s,vh=np.linalg.svd(Cm); rk=int(np.sum(s>1e-9)); K=vh[rk:].T
D=(A@K).T
allv=np.concatenate([np.array(vecs),D])
np.save(out,allv.reshape(-1,p,q)); print(out,allv.shape[0])
