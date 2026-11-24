import numpy as np, itertools, sys
from math import comb
from scipy.optimize import least_squares

PERMS = np.array(list(itertools.permutations(range(4))))

def perm_and_grad(A):
    # A: (S,4,4) -> perm (S,), grad (S,4,4)
    S = A.shape[0]
    P = np.zeros(S, dtype=complex)
    G = np.zeros((S, 4, 4), dtype=complex)
    for p in PERMS:
        f = [A[:, r, p[r]] for r in range(4)]
        P += f[0] * f[1] * f[2] * f[3]
        G[:, 0, p[0]] += f[1] * f[2] * f[3]
        G[:, 1, p[1]] += f[0] * f[2] * f[3]
        G[:, 2, p[2]] += f[0] * f[1] * f[3]
        G[:, 3, p[3]] += f[0] * f[1] * f[2]
    return P, G

def sym_basis():
    Es = []
    for i in range(4):
        for j in range(i, 4):
            E = np.zeros((4, 4)); E[i, j] = 1; E[j, i] = 1
            Es.append(E)
    return np.array(Es, dtype=complex)

def full_basis():
    Es = []
    for i in range(4):
        for j in range(4):
            E = np.zeros((4, 4)); E[i, j] = 1
            Es.append(E)
    return np.array(Es, dtype=complex)

def kernel_of_linear(B, amb):
    _, G = perm_and_grad(B[None].astype(complex))
    q1 = np.einsum('ij,nij->n', G[0], amb)
    u, s, vh = np.linalg.svd(q1.reshape(1, -1))
    K = vh[1:].conj().T
    return np.einsum('na,nij->aij', K, amb)

class Problem:
    def __init__(self, B, amb, m, rng, nsamp=None):
        self.B = B.astype(complex)
        self.pB = perm_and_grad(self.B[None])[0][0]
        self.amb2 = kernel_of_linear(B, amb)
        self.N2 = self.amb2.shape[0]
        self.m = m
        N2 = self.N2
        if nsamp is None:
            nsamp = 2 * comb(m + 4, 4)
        self.Q, _ = np.linalg.qr(rng.normal(size=(N2, N2)) + 1j * rng.normal(size=(N2, N2)))
        self.C = (rng.normal(size=(nsamp, m)) + 1j * rng.normal(size=(nsamp, m))) / np.sqrt(2)
        self.Qamb = np.einsum('nk,nij->kij', self.Q, self.amb2)  # rotated ambient basis
        self.nx = (N2 - m) * m

    def X_of(self, x):
        return (x[: self.nx] + 1j * x[self.nx:]).reshape(self.N2 - self.m, self.m)

    def V_of(self, x):
        X = self.X_of(x)
        W = np.vstack([np.eye(self.m), X])
        return np.einsum('ka,kij->aij', W, self.Qamb)

    def res(self, x):
        V = self.V_of(x)
        T = np.einsum('sa,aij->sij', self.C, V)
        P, _ = perm_and_grad(self.B[None] + T)
        f = P - self.pB
        return np.concatenate([f.real, f.imag])

    def jac(self, x):
        V = self.V_of(x)
        T = np.einsum('sa,aij->sij', self.C, V)
        _, G = perm_and_grad(self.B[None] + T)
        m = self.m
        # d f_s / d X_{k,b} = C_{s b} * <G_s, Qamb_{m+k}>
        g = np.einsum('sij,kij->sk', G, self.Qamb[m:])  # (S, N2-m)
        Jc = (g[:, :, None] * self.C[:, None, :]).reshape(g.shape[0], -1)
        top = np.hstack([Jc.real, -Jc.imag])
        bot = np.hstack([Jc.imag, Jc.real])
        return np.vstack([top, bot])

def normalized_residual(B, V, rng, nsamp=400):
    # orthonormalize the basis V (m,4,4) and evaluate max |perm(B+t)-perm(B)| on unit-ish samples
    m = V.shape[0]
    M = V.reshape(m, -1).T
    Qm, _ = np.linalg.qr(M)
    Vn = Qm.T.reshape(m, 4, 4)
    C = (rng.normal(size=(nsamp, m)) + 1j * rng.normal(size=(nsamp, m))) / np.sqrt(2 * m)
    T = np.einsum('sa,aij->sij', C, Vn)
    P, _ = perm_and_grad(B[None].astype(complex) + T)
    pB = perm_and_grad(B[None].astype(complex))[0][0]
    return np.max(np.abs(P - pB))

def run(B, amb, m, trials, seed=0, maxfev=3000, verbose=True):
    rng = np.random.default_rng(seed)
    results = []
    for tr in range(trials):
        pr = Problem(B, amb, m, rng)
        x0 = rng.normal(size=2 * pr.nx) * rng.choice([0.3, 1.0, 2.0])
        sol = least_squares(pr.res, x0, jac=pr.jac, method='lm', xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=maxfev)
        V = pr.V_of(sol.x)
        nr = normalized_residual(B, V, rng)
        results.append((nr, np.linalg.norm(sol.fun), V))
        if verbose:
            print(tr, 'res', np.linalg.norm(sol.fun), 'normres', nr, '|x|', np.linalg.norm(sol.x), sol.nfev, flush=True)
    results.sort(key=lambda r: r[0])
    return results

def problem_by_name(which):
    if which == '231':
        return np.ones((4, 4)), sym_basis(), 3
    if which == '229':
        return np.ones((4, 4)) + np.eye(4), full_basis(), 6
    kind, m = which[0], int(which[1:])
    if kind == 'J':
        return np.ones((4, 4)), full_basis(), m
    if kind == 'S':
        return np.ones((4, 4)), sym_basis(), m
    if kind == 'D':
        return np.ones((4, 4)) + np.eye(4), full_basis(), m

if __name__ == '__main__':
    which = sys.argv[1]
    trials = int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    B, amb, m = problem_by_name(which)
    results = run(B, amb, m, trials, seed)
    print('BEST normres', results[0][0], 'res', results[0][1])
    np.save('best2_%s_%d.npy' % (which, seed), results[0][2])
