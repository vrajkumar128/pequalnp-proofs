"""Validation of the incremental CEGIS encoder against known minimum sizes.
 a) the 10 five-input monotone shard functions of L-meta-1444 (one-NOT minima from
    onenot_search.py, validated there against brute force for n <= 4): s = min - 1 UNSAT, s = min SAT;
 b) XOR2 / XOR3 / MAJ3 with at most one NOT (4, 9, 4; certified examples of circuit_synth);
 c) the Fano plane (q = 2) line-ORs: monotone 14 found; one-NOT at s = 12 compared with
    circuit_synth (sizes 1..12 UNSAT there)."""
import sys, time
sys.path.insert(0, '.')
from cegis957 import *

ONENOT = {0xfeeafcc0: 6, 0xeeeaeaea: 4, 0xeeeaeee8: 6, 0xeeeeeee0: 4, 0xfee8eee8: 8,
          0xfeeaeaaa: 8, 0xfeeaeae8: 9, 0xfeeaece8: 8, 0xfeeaeee0: 7, 0xfeeafcc8: 7}


def run(n, tabs, s, maxnot, lines=(), tl=600, rows=None, extra_random=0):
    if rows is None:
        rows = set(range(1 << n))
    r = cegis(n, tabs, lines, s, maxnot=maxnot, time_limit=tl, init_rows=rows,
              log=lambda m: None, extra_random=extra_random)
    return r[0]


if __name__ == '__main__':
    what = sys.argv[1]
    ok = True
    t0 = time.time()
    if what == 'a':
        for T, b in ONENOT.items():
            lo = run(5, [T], b - 1, 1)
            hi = run(5, [T], b, 1)
            good = (lo == 'UNSAT' and hi == 'SAT')
            ok &= good
            print('T=%#x one-NOT min %d: s=%d %s, s=%d %s %s' % (T, b, b - 1, lo, b, hi, 'ok' if good else 'MISMATCH'), flush=True)
    if what == 'b':
        for name, n, T, b in (('xor2', 2, 0b0110, 4), ('xor3', 3, 0x96, 9), ('maj3', 3, 0xe8, 4)):
            lo = run(n, [T], b - 1, 1)
            hi = run(n, [T], b, 1)
            good = (lo == 'UNSAT' and hi == 'SAT')
            ok &= good
            print('%s one-NOT min %d: s=%d %s, s=%d %s %s' % (name, b, b - 1, lo, b, hi, 'ok' if good else 'MISMATCH'), flush=True)
    if what == 'c':
        fano = [sorted({(u + w) % 7 for u in (0, 1, 3)}) for w in range(7)]
        tabs = line_tables(7, fano)
        r14 = run(7, tabs, 14, 0, fano)
        r13m = run(7, tabs, 13, 0, fano)
        print('Fano monotone: s=14 %s, s=13 %s' % (r14, r13m), flush=True)
        r12 = run(7, tabs, 12, 1, fano, tl=3000)
        print('Fano one-NOT s=12: %s (circuit_synth: sizes 1..12 UNSAT)' % r12, flush=True)
        ok &= (r14 == 'SAT' and r13m == 'UNSAT' and r12 == 'UNSAT')
    print('VALIDATION %s all ok = %s (%.1fs)' % (what, ok, time.time() - t0), flush=True)
