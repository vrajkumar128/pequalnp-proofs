import numpy as np, sys
from math import comb
from search2 import *
from scipy.optimize import least_squares

class AnsatzProblem:
    """L = span(F) + span(k free vectors in the complement chart)."""
    def __init__(self, B, amb, F, k, rng, nsamp=None):
        self.B=B.astype(complex); self.pB=perm_and_grad(self.B[None])[0][0]
        self.F=F.astype(complex); f=F.shape[0]; self.f=f; self.k=k
        N=amb.shape[0]
        # complement of span F inside amb coordinates
        Fc=np.einsum('aij,nij->an',self.F,amb)  # f x N coords (amb orthonormal basis assumed in matrix inner product)
        u,s,vh=np.linalg.svd(Fc)
        comp=vh[f:].conj()   # (N-f) x N
        compmats=np.einsum('rn,nij->rij',comp,amb)
        R=compmats.shape[0]
        Q,_=np.linalg.qr(rng.normal(size=(R,R))+1j*rng.normal(size=(R,R)))
        self.Qamb=np.einsum('rk,rij->kij',Q,compmats)
        self.R=R; self.nx=(R-k)*k
        m=f+k
        if nsamp is None: nsamp=2*comb(m+4,4)
        self.C=(rng.normal(size=(nsamp,m))+1j*rng.normal(size=(nsamp,m)))/np.sqrt(2)
    def X_of(self,x): return (x[:self.nx]+1j*x[self.nx:]).reshape(self.R-self.k,self.k)
    def V_of(self,x):
        W=np.vstack([np.eye(self.k),self.X_of(x)])
        U=np.einsum('ka,kij->aij',W,self.Qamb)
        return np.concatenate([self.F,U])
    def res(self,x):
        V=self.V_of(x); T=np.einsum('sa,aij->sij',self.C,V)
        P,_=perm_and_grad(self.B[None]+T); f=P-self.pB
        return np.concatenate([f.real,f.imag])
    def jac(self,x):
        V=self.V_of(x); T=np.einsum('sa,aij->sij',self.C,V)
        _,G=perm_and_grad(self.B[None]+T)
        g=np.einsum('sij,kij->sk',G,self.Qamb[self.k:])
        Ck=self.C[:,self.f:]
        Jc=(g[:,:,None]*Ck[:,None,:]).reshape(g.shape[0],-1)
        return np.vstack([np.hstack([Jc.real,-Jc.imag]),np.hstack([Jc.imag,Jc.real])])

def col_space(B,c):
    # column c supported, with zero first-order change
    _,G=perm_and_grad(B[None].astype(complex))
    g=G[0][:,c]
    u,s,vh=np.linalg.svd(g.reshape(1,-1)); K=vh[1:].conj()
    F=[]
    for kv in K:
        E=np.zeros((4,4),dtype=complex); E[:,c]=kv; F.append(E)
    return np.array(F)

def row_space(B,r):
    return np.array([E.T for E in col_space(B.T,r)])

if __name__=='__main__':
    which=sys.argv[1]; k=int(sys.argv[2]); trials=int(sys.argv[3]); seed=int(sys.argv[4]); fam=sys.argv[5]
    B,amb,m=problem_by_name(which)
    rng=np.random.default_rng(seed)
    if fam=='col0': F=col_space(B,0)
    elif fam=='row0': F=row_space(B,0)
    elif fam=='sym2':
        F=[]
        for b in [np.array([0,1,-1,0.]),np.array([0,0,1,-1.])]:
            E=np.zeros((4,4)); E[0,:]+=b; E[:,0]+=b; F.append(E)
        F=np.array(F,dtype=complex)
    best=[]
    for tr in range(trials):
        pr=AnsatzProblem(B,amb,F,k,rng)
        x0=rng.normal(size=2*pr.nx)*rng.choice([0.3,1.0,2.0])
        sol=least_squares(pr.res,x0,jac=pr.jac,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=3000)
        V=pr.V_of(sol.x); nr=normalized_residual(B,V,rng)
        best.append((nr,V))
        print(tr,'nr %.3e'%nr,'nfev',sol.nfev,flush=True)
    best.sort(key=lambda z:z[0])
    print('BEST',best[0][0])
    np.save('ans_%s_%s_%d_%d.npy'%(which,fam,k,seed),best[0][1])
