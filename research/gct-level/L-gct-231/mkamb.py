import numpy as np, sys
q=int(sys.argv[1]); kind=sys.argv[2]
a=np.array([1,1j,-1,-1j]); c=np.array([1,-1,1,-1]); b=np.array([1,-1j,-1,1j])
# basis of 1-perp in C^q
P=np.eye(q)-np.ones((q,q))/q
u,s,vh=np.linalg.svd(P); E=vh[:q-1]
vecs={'a':a,'b':b,'c':c}
out=[]
for k in kind:
    for e in E:
        out.append(np.outer(vecs[k],e))
np.save('amb_%d_%s.npy'%(q,kind),np.array(out))
print(len(out))
