"""Timings for the README: python scripts/bench.py (uses python-sat CaDiCaL 1.9.5 in-process)."""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from circuit_synth import Target, Basis, Problem, minimum, find  # noqa: E402
from circuit_synth.synth import run_size  # noqa: E402

PETERSEN = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
            (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]


def maj(n, k):
    return sum(1 << t for t in range(1 << n) if bin(t).count('1') >= k)


def bench(label, prob, sizes, timeout=None):
    if timeout:
        prob.backend = 'kissat'
    for s in sizes:
        t0 = time.time()
        rec, c = run_size(prob, s, timeout=timeout)
        print('%-46s s=%2d %-5s %7.2fs  (%d vars, %d clauses)' % (
            label, s, rec['status'], time.time() - t0, rec.get('vars', 0), rec.get('clauses', 0)),
            flush=True)


if __name__ == '__main__':
    which = sys.argv[1:] or ['small', 'mid']
    if 'small' in which:
        bench('C5 edge fn, mono, minterm rows', Problem(Target.graph(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]).monotone_rows(), Basis(0)), [6, 7])
        bench('C5 edge fn, mono, full rows', Problem(Target.graph(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]), Basis(0)), [6, 7])
        bench('C5 edge fn, mono, RAW, minterm rows', Problem(Target.graph(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]).monotone_rows(), Basis(0), 'raw'), [6, 7])
        bench('XOR3 <=1 NOT', Problem(Target(3, [0x96]), Basis(1)), [8, 9])
        bench('XOR3 full', Problem(Target(3, [0x96]), Basis(None)), [7, 8])
        bench('MAJ5 (3 of 5) mono, minterm rows', Problem(Target(5, [maj(5, 3)]).monotone_rows(), Basis(0)), [10])
    if 'mid' in which:
        bench('MAJ5 (3 of 5) mono, minterm rows, kissat', Problem(Target(5, [maj(5, 3)]).monotone_rows(), Basis(0)), [9], timeout=240)
        bench('XOR4 full, kissat', Problem(Target(4, [0x6996]), Basis(None)), [12], timeout=240)
        bench('Petersen edge fn, mono, minterm rows, kissat', Problem(Target.graph(10, PETERSEN).monotone_rows(), Basis(0)), [20], timeout=420)
        T8 = Target.monotone_from_minterms(8, [[0, 1], [2, 3], [4, 5], [6, 7], [1, 2, 5]])
        bench('8-input DNF (5 terms), full 256 rows, full basis', Problem(T8, Basis(None)), [9, 8], timeout=120)
