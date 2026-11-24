import numpy as np, sys
from search3 import PermPQ, ambient
rng=np.random.default_rng(0)
def rowcol_space(p,q):
    V=[]
    for j in range(1,q):   # row 0: b with sum 0: e_j - e_0
        E=np.zeros((p,q)); E[0,j]=1; E[0,0]=-1; V.append(E)
    for i in range(2,p):   # column 0: a with a_0=0, sum 0: e_i - e_1
        E=np.zeros((p,q)); E[i,0]=1; E[1,0]=-1; V.append(E)
    return np.array(V,dtype=complex)
def check_and_ext(p,q,V,amb):
    pp=PermPQ(p,q); B=np.ones((1,p,q))
    m=V.shape[0]
    C=rng.normal(size=(300,m))+1j*rng.normal(size=(300,m))
    T=np.einsum('sa,aij->sij',C,V)
    P,G=pp.val_grad(B+T); P0=pp.val_grad(B.astype(complex))[0][0]
    lev=np.max(np.abs(P-P0))/np.max(np.abs(P))
    Mx=np.einsum('sij,nij->sn',G,amb)
    sv=np.linalg.svd(Mx,compute_uv=False); sv/=sv[0]
    return lev, amb.shape[0]-np.sum(sv>1e-9)
for (p,q) in [(4,4),(4,5),(5,5),(4,6),(3,4)]:
    V=rowcol_space(p,q); amb=ambient(p,q)
    lev,ext=check_and_ext(p,q,V,amb)
    print(p,q,'dim',V.shape[0],'level rel err %.1e'%lev,'first-order ext dim',ext)
print('--- test the extra direction')
for (p,q) in [(4,4),(4,5),(5,5),(4,6),(3,4)]:
    V=rowcol_space(p,q); amb=ambient(p,q); pp=PermPQ(p,q); B=np.ones((1,p,q))
    m=V.shape[0]
    C=rng.normal(size=(400,m))+1j*rng.normal(size=(400,m))
    T=np.einsum('sa,aij->sij',C,V)
    _,G=pp.val_grad(B+T)
    Mx=np.einsum('sij,nij->sn',G,amb)
    u,s,vh=np.linalg.svd(Mx); s/=s[0]
    ns=vh[np.sum(s>1e-9):].conj()   # null vectors in amb coords
    U=np.einsum('kn,nij->kij',ns,amb)
    # component outside span V
    Vm=V.reshape(m,-1).T; Um=U.reshape(U.shape[0],-1).T
    proj=Um-Vm@np.linalg.lstsq(Vm,Um,rcond=None)[0]
    k=np.argmax(np.linalg.norm(proj,axis=0)); u0=proj[:,k].reshape(p,q)
    print(p,q,'extra direction (rounded):'); print(np.round(u0/np.max(np.abs(u0)),3))
    W=np.concatenate([V,u0[None]])
    C2=rng.normal(size=(400,m+1))+1j*rng.normal(size=(400,m+1))
    P,_=pp.val_grad(B+np.einsum('sa,aij->sij',C2,W)); P0=pp.val_grad(B.astype(complex))[0][0]
    print('  span(L,u0) level err', np.max(np.abs(P-P0)))
