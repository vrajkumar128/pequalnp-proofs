import numpy as np, itertools, sys
from scipy.optimize import least_squares

PERMS = np.array(list(itertools.permutations(range(4))))

def perm4(A):
    # A: (..., 4, 4)
    r = np.zeros(A.shape[:-2], dtype=complex)
    for p in PERMS:
        r = r + A[..., 0, p[0]] * A[..., 1, p[1]] * A[..., 2, p[2]] * A[..., 3, p[3]]
    return r

def sym_basis():
    Es = []
    for i in range(4):
        for j in range(i, 4):
            E = np.zeros((4, 4)); E[i, j] = 1; E[j, i] = 1
            Es.append(E)
    return np.array(Es)

def full_basis():
    Es = []
    for i in range(4):
        for j in range(4):
            E = np.zeros((4, 4)); E[i, j] = 1
            Es.append(E)
    return np.array(Es)

def setup(B, amb, m, nsamp, rng):
    # amb: (N,4,4) basis of ambient space
    N = amb.shape[0]
    # restrict to kernel of linear part Q1: Q1(E) = d/ds perm(B + sE)
    eps = 1e-6
    q1 = np.array([(perm4(B + eps * E) - perm4(B - eps * E)) / (2 * eps) for E in amb])
    # kernel basis of q1 (row vector)
    u, s, vh = np.linalg.svd(q1.reshape(1, -1))
    K = vh[1:].conj().T  # N x (N-1), columns orthonormal kernel
    amb2 = np.einsum('na,nij->aij', K, amb)  # (N-1) basis matrices
    N2 = amb2.shape[0]
    Q, _ = np.linalg.qr(rng.normal(size=(N2, N2)) + 1j * rng.normal(size=(N2, N2)))
    C = (rng.normal(size=(nsamp, m)) + 1j * rng.normal(size=(nsamp, m))) / np.sqrt(2)
    return amb2, Q, C

def make_fun(B, amb2, Q, C, m):
    N2 = amb2.shape[0]
    pB = perm4(B)
    def W_of(x):
        X = (x[: (N2 - m) * m] + 1j * x[(N2 - m) * m:]).reshape(N2 - m, m)
        W = Q @ np.vstack([np.eye(m), X])  # N2 x m
        return W
    def res(x):
        W = W_of(x)
        V = np.einsum('na,nij->aij', W, amb2)  # m basis matrices
        T = np.einsum('sa,aij->sij', C, V)
        f = perm4(B[None] + T) - pB
        return np.concatenate([f.real, f.imag])
    return res, W_of

def run(B, amb, m, trials, seed=0, nsamp=None):
    rng = np.random.default_rng(seed)
    from math import comb
    if nsamp is None:
        nsamp = 2 * comb(m + 4, 4)
    best = (np.inf, None)
    for tr in range(trials):
        amb2, Q, C = setup(B, amb, m, nsamp, rng)
        res, W_of = make_fun(B, amb2, Q, C, m)
        N2 = amb2.shape[0]
        x0 = rng.normal(size=2 * (N2 - m) * m) * rng.choice([0.3, 1.0, 3.0])
        try:
            sol = least_squares(res, x0, method='lm', xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        except Exception as e:
            continue
        r = np.linalg.norm(sol.fun)
        W = W_of(sol.x)
        cond = np.linalg.cond(W)
        if r < best[0]:
            best = (r, np.einsum('na,nij->aij', W, amb2))
        print(tr, 'res', r, 'cond', cond, flush=True)
    return best

if __name__ == '__main__':
    which = sys.argv[1]
    trials = int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    if which == '231':
        B = np.ones((4, 4)); amb = sym_basis(); m = 3
    elif which == '229':
        B = np.ones((4, 4)) + np.eye(4); amb = full_basis(); m = 6
    elif which.startswith('J'):
        m = int(which[1:]); B = np.ones((4, 4)); amb = full_basis()
    elif which.startswith('S'):
        m = int(which[1:]); B = np.ones((4, 4)); amb = sym_basis()
    elif which.startswith('D'):
        m = int(which[1:]); B = np.ones((4, 4)) + np.eye(4); amb = full_basis()
    best = run(B, amb, m, trials, seed)
    print('BEST', best[0])
    np.save('best_%s_%d.npy' % (which, seed), best[1])
