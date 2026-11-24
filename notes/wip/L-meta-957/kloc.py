"""K-local cases: the lines outside K are computed by private OR trees (3 gates each, no NOT);
every OR of 2, 3 or 4 points of each such line is offered as a free library wire (a superset of
what any choice of tree shapes provides). The remaining 38 - 3(13-k) = 3k - 1 gates, with at
most one NOT, must compute the k lines of K. UNSAT => no 38-gate one-NOT circuit of this shape.
K runs over orbit representatives of k-sets of lines under PGL(3,3)."""
import sys, time, itertools
sys.path.insert(0, '.')
from cegis957 import *
from plane import collineations, orbits_of_line_sets

n = 13
ALL = line_tables()
FULLR = 1 << n


def or_table(T):
    m = 0
    for t in range(FULLR):
        if any((t >> i) & 1 for i in T):
            m |= 1 << t
    return m


def library(K):
    lib, names = [], []
    for w in range(13):
        if w in K:
            continue
        L = LINES[w]
        for r in (2, 3, 4):
            for T in itertools.combinations(L, r):
                lib.append(or_table(T))
                names.append(T)
    return lib, names


if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1].split(',')]
    tl = float(sys.argv[2])
    G = collineations()
    for k in ks:
        for K, size in orbits_of_line_sets(G, k):
            lib, names = library(K)
            tabs = [ALL[w] for w in K]
            s = 3 * k - 1
            t0 = time.time()
            print('K=%s (orbit %d) free gates %d, library %d wires' % (K, size, s, len(lib)), flush=True)
            r = cegis(n, tabs, [LINES[w] for w in K], s, maxnot=1, lib=lib, time_limit=tl,
                      log=lambda m: print(m, flush=True))
            print('RESULT k=%d K=%s s=%d -> %s (%d iterations, %.1fs)' % (k, K, s, r[0], r[3], time.time() - t0), flush=True)
            if r[1]:
                print('  circuit', r[1], flush=True)
                print('  library names', names, flush=True)
