"""PG(2,3) as lines {0,1,3,9}+w mod 13: collineation group (as point permutations), orbits."""
import itertools
from cegis957 import LINES

N = 13
LSET = [frozenset(L) for L in LINES]
LINE_OF = {}
for w, L in enumerate(LSET):
    for a, b in itertools.combinations(sorted(L), 2):
        LINE_OF[(a, b)] = w
        LINE_OF[(b, a)] = w


def collinear(a, b, c):
    if a == b or b == c or a == c:
        return True
    return c in LSET[LINE_OF[(a, b)]]


def collineations():
    """All permutations of the 13 points mapping lines to lines (backtracking)."""
    out = []
    img = [None] * N
    used = [False] * N

    def ok(k):
        for a, b in itertools.combinations(range(k), 2):
            c = k
            if collinear(a, b, c) != collinear(img[a], img[b], img[c]):
                return False
        return True

    def rec(k):
        if k == N:
            out.append(tuple(img))
            return
        for v in range(N):
            if used[v]:
                continue
            img[k] = v
            if ok(k):
                used[v] = True
                rec(k + 1)
                used[v] = False
            img[k] = None
    rec(0)
    return out


def line_perm(g):
    """Induced permutation of lines."""
    idx = {L: w for w, L in enumerate(LSET)}
    return tuple(idx[frozenset(g[p] for p in L)] for L in LSET)


def orbits_of_line_sets(G, k):
    LP = [line_perm(g) for g in G]
    seen = set()
    reps = []
    for K in itertools.combinations(range(N), k):
        K = frozenset(K)
        if K in seen:
            continue
        orb = {frozenset(lp[w] for w in K) for lp in LP}
        seen |= orb
        reps.append((tuple(sorted(K)), len(orb)))
    return reps


if __name__ == '__main__':
    G = collineations()
    print('group order', len(G))
    for k in range(1, 8):
        r = orbits_of_line_sets(G, k)
        print(k, len(r), r)
