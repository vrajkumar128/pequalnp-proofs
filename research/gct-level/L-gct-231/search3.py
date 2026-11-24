import numpy as np, itertools, sys, time
from math import comb
from scipy.optimize import least_squares

def injections(p, q):
    return np.array(list(itertools.permutations(range(q), p)))

class PermPQ:
    def __init__(self, p, q):
        self.p, self.q = p, q
        self.F = injections(p, q)
    def val_grad(self, A):
        # A: (S,p,q) -> sum_f prod_i A[:, i, f_i], gradient (S,p,q)
        S = A.shape[0]; p = self.p
        P = np.zeros(S, dtype=complex)
        G = np.zeros((S, p, self.q), dtype=complex)
        for f in self.F:
            fac = [A[:, i, f[i]] for i in range(p)]
            pre = [np.ones(S, dtype=complex)]
            for i in range(p):
                pre.append(pre[-1] * fac[i])
            suf = np.ones(S, dtype=complex)
            P += pre[p]
            for i in range(p - 1, -1, -1):
                G[:, i, f[i]] += pre[i] * suf
                suf = suf * fac[i]
        return P, G

def ambient(p, q, rowzero=False, colzero=False):
    N = p * q
    cons = []
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
    def __init__(self, pp, B, amb, m, rng, oversample=1.3):
        self.pp = pp
        self.B = B.astype(complex)
        P0, G0 = pp.val_grad(self.B[None])
        self.pB = P0[0]
        q1 = np.einsum('ij,nij->n', G0[0], amb)
        if np.linalg.norm(q1) > 1e-9:
            u, s, vh = np.linalg.svd(q1.reshape(1, -1))
            K = vh[1:].conj().T
            amb2 = np.einsum('na,nij->aij', K, amb)
        else:
            amb2 = amb
        self.amb2 = amb2
        self.N2 = amb2.shape[0]
        self.m = m
        N2 = self.N2
        nmon = comb(m + pp.p, pp.p)
        nsamp = int(oversample * nmon) + 10
        Q, _ = np.linalg.qr(rng.normal(size=(N2, N2)) + 1j * rng.normal(size=(N2, N2)))
        self.Qamb = np.einsum('nk,nij->kij', Q, amb2)
        self.C = (rng.normal(size=(nsamp, m)) + 1j * rng.normal(size=(nsamp, m))) / np.sqrt(2)
        self.nx = (N2 - m) * m

    def V_of(self, x):
        X = (x[: self.nx] + 1j * x[self.nx:]).reshape(self.N2 - self.m, self.m)
        W = np.vstack([np.eye(self.m), X])
        return np.einsum('ka,kij->aij', W, self.Qamb)

    def res(self, x):
        V = self.V_of(x)
        T = np.einsum('sa,aij->sij', self.C, V)
        P, _ = self.pp.val_grad(self.B[None] + T)
        f = P - self.pB
        return np.concatenate([f.real, f.imag])

    def jac(self, x):
        V = self.V_of(x)
        T = np.einsum('sa,aij->sij', self.C, V)
        _, G = self.pp.val_grad(self.B[None] + T)
        m = self.m
        g = np.einsum('sij,kij->sk', G, self.Qamb[m:])
        Jc = (g[:, :, None] * self.C[:, None, :]).reshape(g.shape[0], -1)
        return np.vstack([np.hstack([Jc.real, -Jc.imag]), np.hstack([Jc.imag, Jc.real])])

def normalized_residual(pp, B, V, rng, nsamp=400):
    m = V.shape[0]
    M = V.reshape(m, -1).T
    Qm, _ = np.linalg.qr(M)
    Vn = Qm.T.reshape(m, *V.shape[1:])
    C = (rng.normal(size=(nsamp, m)) + 1j * rng.normal(size=(nsamp, m))) / np.sqrt(2 * m)
    T = np.einsum('sa,aij->sij', C, Vn)
    P, _ = pp.val_grad(B[None].astype(complex) + T)
    pB = pp.val_grad(B[None].astype(complex))[0][0]
    return np.max(np.abs(P - pB))

def run(p, q, m, trials, seed, rowzero=False, colzero=False, maxfev=int(__import__("os").environ.get("MAXFEV","2000")), tag=''):
    rng = np.random.default_rng(seed)
    pp = PermPQ(p, q)
    B = np.ones((p, q))
    amb = ambient(p, q, rowzero, colzero)
    best = None
    for tr in range(trials):
        t0 = time.time()
        pr = Problem(pp, B, amb, m, rng)
        x0 = rng.normal(size=2 * pr.nx) * rng.choice([0.3, 1.0, 2.0])
        sol = least_squares(pr.res, x0, jac=pr.jac, method='lm', xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=maxfev)
        V = pr.V_of(sol.x)
        nr = normalized_residual(pp, B, V, rng)
        if nr < 1e-8:
            np.save('sols/%s_t%d.npy' % (tag, tr), V)
        if best is None or nr < best[0]:
            best = (nr, V)
            np.save('best3_%s.npy' % tag, V)
        print(tr, 'normres %.3e' % nr, 'nfev', sol.nfev, 'time %.1f' % (time.time() - t0), flush=True)
    print('BEST', best[0], flush=True)
    return best

if __name__ == '__main__':
    p, q, m, trials, seed = map(int, sys.argv[1:6])
    flags = sys.argv[6] if len(sys.argv) > 6 else ''
    tag = '%dx%d_m%d_%s_s%d' % (p, q, m, flags or 'none', seed)
    run(p, q, m, trials, seed, rowzero='r' in flags, colzero='c' in flags, tag=tag)
