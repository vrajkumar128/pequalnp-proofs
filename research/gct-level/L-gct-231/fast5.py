import os
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np, itertools, sys, time
from math import comb

class PermPQ:
    def __init__(self, p, q):
        self.p, self.q = p, q
        F = np.array(list(itertools.permutations(range(q), p)))
        self.F = F
        self.nf = len(F)
        self.flat = (np.arange(p)[None, :] * q + F)  # (nf, p) flat indices
        oh = np.zeros((self.nf, p, p * q))
        for f in range(self.nf):
            for i in range(p):
                oh[f, i, self.flat[f, i]] = 1
        self.onehot = oh.reshape(self.nf * p, p * q)

    def val_grad(self, A):
        S = A.shape[0]
        Af = A.reshape(S, -1)
        X = Af[:, self.flat]  # (S, nf, p)
        p = self.p
        pre = np.ones((S, self.nf, p + 1), dtype=complex)
        for i in range(p):
            pre[:, :, i + 1] = pre[:, :, i] * X[:, :, i]
        suf = np.ones((S, self.nf, p + 1), dtype=complex)
        for i in range(p - 1, -1, -1):
            suf[:, :, i] = suf[:, :, i + 1] * X[:, :, i]
        P = pre[:, :, p].sum(axis=1)
        gr = pre[:, :, :p] * suf[:, :, 1:]  # (S, nf, p)
        G = (gr.reshape(S, -1) @ self.onehot).reshape(S, p, self.q)
        return P, G

def ambient(p, q, rowzero=False, colzero=False, sym=False):
    N = p * q
    cons = []
    if sym:
        for i in range(p):
            for j in range(i + 1, q):
                r = np.zeros((p, q)); r[i, j] = 1; r[j, i] = -1; cons.append(r.ravel())
    if rowzero:
        for i in range(p):
            r = np.zeros((p, q)); r[i, :] = 1; cons.append(r.ravel())
    if colzero:
        for j in range(q):
            c = np.zeros((p, q)); c[:, j] = 1; cons.append(c.ravel())
    if cons:
        A = np.array(cons)
        u, s, vh = np.linalg.svd(A)
        rank = int(np.sum(s > 1e-9))
        K = vh[rank:]
    else:
        K = np.eye(N)
    return K.reshape(-1, p, q).astype(complex)

class Problem:
    def __init__(self, pp, amb, m, rng, oversample=1.15, diag=0.0):
        self.pp = pp
        p, q = pp.p, pp.q
        self.B = np.ones((1, p, q), dtype=complex)
        for i in range(min(p, q)):
            self.B[0, i, i] += diag
        P0, G0 = pp.val_grad(self.B)
        self.pB = P0[0]
        q1 = np.einsum('ij,nij->n', G0[0], amb)
        if np.linalg.norm(q1) > 1e-9:
            u, s, vh = np.linalg.svd(q1.reshape(1, -1))
            K = vh[1:].conj().T
            amb = np.einsum('na,nij->aij', K, amb)
        self.N2 = amb.shape[0]
        self.m = m
        N2 = self.N2
        nmon = comb(m + p, p) - 1 - m
        nsamp = int(oversample * nmon) + 10
        Q, _ = np.linalg.qr(rng.normal(size=(N2, N2)) + 1j * rng.normal(size=(N2, N2)))
        self.Qamb = np.einsum('nk,nij->kij', Q, amb).reshape(N2, -1)
        self.C = (rng.normal(size=(nsamp, m)) + 1j * rng.normal(size=(nsamp, m))) / np.sqrt(2)
        self.shape = (p, q)

    def V_of(self, X):
        W = np.vstack([np.eye(self.m), X])
        return (W.T @ self.Qamb).reshape(self.m, *self.shape)

    def res_jac(self, X, need_jac=True):
        V = self.V_of(X)
        T = (self.C @ V.reshape(self.m, -1)).reshape(-1, *self.shape)
        P, G = self.pp.val_grad(self.B + T)
        r = P - self.pB
        if not need_jac:
            return r, None
        g = G.reshape(G.shape[0], -1) @ self.Qamb[self.m:].T  # (S, N2-m)
        J = (g[:, :, None] * self.C[:, None, :]).reshape(g.shape[0], -1)
        return r, J

def lm(pr, X0, iters=1500, lam=1e-2, tol=1e-28):
    X = X0.copy()
    r, J = pr.res_jac(X)
    f = np.vdot(r, r).real
    shp = X.shape
    hist = []
    for it in range(iters):
        JH = J.conj().T
        A = JH @ J
        g = JH @ r
        d = np.diag(A).real.copy()
        improved = False
        for _ in range(12):
            try:
                step = np.linalg.solve(A + lam * np.diag(d + 1e-12), -g)
            except np.linalg.LinAlgError:
                lam *= 10; continue
            Xn = X + step.reshape(shp)
            rn, _ = pr.res_jac(Xn, need_jac=False)
            fn = np.vdot(rn, rn).real
            if fn < f:
                X = Xn; f = fn; lam = max(lam / 3, 1e-15); improved = True
                break
            lam *= 4
        if not improved or f < tol:
            break
        hist.append(f)
        if len(hist) > 60 and hist[-60] < 1.02 * f:
            break
        r, J = pr.res_jac(X)
    return X, f, it

def normalized_residual(pp, V, rng, nsamp=400, diag=0.0):
    m = V.shape[0]
    M = V.reshape(m, -1).T
    Qm, _ = np.linalg.qr(M)
    Vn = Qm.T.reshape(m, *V.shape[1:])
    C = (rng.normal(size=(nsamp, m)) + 1j * rng.normal(size=(nsamp, m))) / np.sqrt(2 * m)
    T = np.einsum('sa,aij->sij', C, Vn)
    B = np.ones((1,) + V.shape[1:], dtype=complex)
    for i in range(min(V.shape[1:])):
        B[0, i, i] += diag
    P, _ = pp.val_grad(B + T)
    pB = pp.val_grad(B)[0][0]
    return np.max(np.abs(P - pB))

def run(p, q, m, trials, seed, rowzero=False, colzero=False, iters=1500, tag='', sym=False, diag=0.0):
    rng = np.random.default_rng(seed)
    pp = PermPQ(p, q)
    amb = ambient(p, q, rowzero, colzero, sym)
    if os.environ.get('AMB'):
        A = np.load(os.environ['AMB']).reshape(-1, p * q)
        Qa, _ = np.linalg.qr(A.T)
        amb = Qa.T.reshape(-1, p, q).astype(complex)
    best = None
    for tr in range(trials):
        t0 = time.time()
        pr = Problem(pp, amb, m, rng, diag=diag)
        sc = rng.choice([0.3, 1.0, 2.0])
        X0 = sc * (rng.normal(size=(pr.N2 - m, m)) + 1j * rng.normal(size=(pr.N2 - m, m))) / np.sqrt(2)
        X, f, it = lm(pr, X0, iters=iters)
        V = pr.V_of(X)
        nr = normalized_residual(pp, V, rng, diag=diag)
        if nr < 1e-8:
            np.save('sols/%s_t%d.npy' % (tag, tr), V)
        if best is None or nr < best[0]:
            best = (nr, V)
            np.save('best4_%s.npy' % tag, V)
        print(tr, 'normres %.3e' % nr, 'iters', it, 'time %.1f' % (time.time() - t0), flush=True)
    print('BEST', best[0], flush=True)
    return best

if __name__ == '__main__':
    p, q, m, trials, seed = map(int, sys.argv[1:6])
    flags = sys.argv[6] if len(sys.argv) > 6 else ''
    iters = int(os.environ.get('ITERS', '1500'))
    tag = 'f_%dx%d_m%d_%s_s%d' % (p, q, m, flags or 'none', seed)
    diag = float(os.environ.get('DIAG', '0'))
    if diag: tag += '_d%g' % diag
    run(p, q, m, trials, seed, rowzero='r' in flags, colzero='c' in flags, iters=iters, tag=tag, sym='s' in flags, diag=diag)
