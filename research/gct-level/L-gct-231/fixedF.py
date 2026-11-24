import os
os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np, sys, time
from math import comb
from fast5 import PermPQ, lm, normalized_residual

class FProblem:
    """L = span(F) + span(k vectors from ambient amb)."""
    def __init__(self, pp, F, amb, k, rng, oversample=1.15):
        self.pp=pp; p,q=pp.p,pp.q; self.shape=(p,q)
        self.B=np.ones((1,p,q),dtype=complex); self.pB=pp.val_grad(self.B)[0][0]
        self.F=F.reshape(F.shape[0],-1).astype(complex); f=F.shape[0]; self.f=f; self.m=k
        A=amb.reshape(amb.shape[0],-1).astype(complex)
        # remove span F from amb
        Qf,_=np.linalg.qr(self.F.T)
        A=A-(A@Qf.conj())@Qf.T
        u,s,vh=np.linalg.svd(A,full_matrices=False); r=int(np.sum(s>1e-9*s[0])); A=vh[:r]
        # remove linear-level direction (S1) if present
        _,G0=pp.val_grad(self.B); g=A.conj()@G0[0].ravel()
        if np.linalg.norm(g)>1e-9:
            u2,s2,vh2=np.linalg.svd(g.reshape(1,-1)); A=vh2[1:].conj()@A
        N2=A.shape[0]; self.N2=N2
        Q,_=np.linalg.qr(rng.normal(size=(N2,N2))+1j*rng.normal(size=(N2,N2)))
        self.Qamb=Q.T@A
        mt=f+k
        nmon=comb(mt+p,p)-1-mt
        nsamp=int(oversample*nmon)+10
        self.Ct=(rng.normal(size=(nsamp,mt))+1j*rng.normal(size=(nsamp,mt)))/np.sqrt(2)
        self.C=self.Ct[:,f:]
    def V_of(self,X):
        W=np.vstack([np.eye(self.m),X])
        U=W.T@self.Qamb
        return np.concatenate([self.F,U]).reshape(-1,*self.shape)
    def res_jac(self,X,need_jac=True):
        V=self.V_of(X); T=(self.Ct@V.reshape(V.shape[0],-1)).reshape(-1,*self.shape)
        P,G=self.pp.val_grad(self.B+T); r=P-self.pB
        if not need_jac: return r,None
        g=G.reshape(G.shape[0],-1)@self.Qamb[self.m:].T
        J=(g[:,:,None]*self.C[:,None,:]).reshape(g.shape[0],-1)
        return r,J

if __name__=='__main__':
    p,q,k,trials,seed=map(int,sys.argv[1:6]); Ffile=sys.argv[6]; ambfile=sys.argv[7]; tag=sys.argv[8]
    F=np.load(Ffile); amb=np.load(ambfile)
    pp=PermPQ(p,q); rng=np.random.default_rng(seed); best=None
    for tr in range(trials):
        t0=time.time()
        pr=FProblem(pp,F,amb,k,rng)
        sc=rng.choice([0.3,1.0,2.0])
        X0=sc*(rng.normal(size=(pr.N2-k,k))+1j*rng.normal(size=(pr.N2-k,k)))/np.sqrt(2)
        X,f,it=lm(pr,X0,iters=1500)
        V=pr.V_of(X); nr=normalized_residual(pp,V,rng)
        if nr<1e-8: np.save('sols/F_%s_t%d.npy'%(tag,tr),V)
        if best is None or nr<best: best=nr
        print(tr,'normres %.3e'%nr,'iters',it,'time %.1f'%(time.time()-t0),flush=True)
    print('BEST',best,flush=True)
