"""Checks for the size-13 case split.

1. The automorphism group of the Fano plane (lines {0,1,3}+w mod 7) has order 168 and is
   2-transitive on points (used by the symmetry lemma).
2. Empirical test of the symmetry lemma on the tool's NF encoding: for 2-transitive Boolean-sum
   systems and every size s up to min+2, with <= 1 NOT,
       base(s) SAT  <=>  base(s) + one of the three first-gate cubes SAT
   (NOT x0 / OR(x0,x1) / AND(x0,x1)). "<=" is trivial; "=>" is the lemma.
   Also: Fano at s = 14 and 15 (SAT) has a solution in some cube.
3. Coverage of the NOT-position sub-split (propositional, checked by unit propagation):
   base(13) & cube_G & (some isnot_j) & no isnot_j for j >= 1  is refuted by unit propagation
   for G = OR(x0,x1) and AND(x0,x1); written as CNFs and checked by drat-trim (empty proof).
"""
import itertools
import os
import subprocess
import sys
import time

TOOL = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth'
sys.path.insert(0, TOOL)
from pysat.solvers import Solver                       # noqa: E402
from circuit_synth.core import Target, Basis          # noqa: E402
from circuit_synth.encode import SB                    # noqa: E402
from circuit_synth.synth import Problem               # noqa: E402

FANO = [sorted({(u + w) % 7 for u in (0, 1, 3)}) for w in range(7)]


def automorphisms(n, lines):
    L = set(frozenset(x) for x in lines)
    return [p for p in itertools.permutations(range(n))
            if set(frozenset(p[i] for i in l) for l in L) == L]


def cubes(meta):
    A, B, op = meta['A'], meta['B'], meta['op']
    return {'not_x0': [A[0][0], B[0][0]], 'or_x0x1': [A[0][0], B[0][1], -op[0]],
            'and_x0x1': [A[0][0], B[0][1], op[0]]}


def solve(clauses, assumptions=()):
    with Solver(name='cadical195', bootstrap_with=clauses) as sv:
        return sv.solve(assumptions=list(assumptions))


def check_system(name, n, sets, smax):
    G = automorphisms(n, sets)
    two_trans = len({(p[0], p[1]) for p in G}) == n * (n - 1)
    prob = Problem(Target.boolean_sums(n, sets), Basis(1), 'nf', SB())
    ok = True
    for s in range(1, smax + 1):
        inst, reason = prob.encode(s)
        if inst is None:
            continue
        cl = inst.cnf.clauses
        base = solve(cl)
        cs = {k: solve(cl, c) for k, c in cubes(inst.meta).items()}
        good = base == any(cs.values())
        ok &= good
        print('  %s s=%d base %s cubes %s %s' % (name, s, 'SAT' if base else 'UNSAT',
              {k: int(v) for k, v in cs.items()}, 'ok' if good else 'MISMATCH'), flush=True)
    print('%s: |Aut| = %d, 2-transitive %s, lemma holds on all sizes: %s' % (
        name, len(G), two_trans, ok), flush=True)
    return ok and two_trans


def coverage(out):
    prob = Problem(Target.boolean_sums(7, FANO), Basis(1), 'nf', SB())
    inst, _ = prob.encode(13)
    isnot = inst.meta['isnot']
    res = True
    for g in ('or_x0x1', 'and_x0x1'):
        extra = [cubes(inst.meta)[g], [isnot[j] for j in range(13)]] + \
            [[-isnot[j]] for j in range(1, 13)]
        cl = [list(c) for c in inst.cnf.clauses] + [[l] for l in extra[0]] + extra[1:]
        with Solver(name='cadical195', bootstrap_with=cl) as sv:
            st, _ = sv.propagate(assumptions=[])
        fn = os.path.join(out, 'coverage_%s.cnf' % g)
        with open(fn, 'w') as f:
            f.write('c coverage of the NOT-position split for first gate %s:\n' % g)
            f.write('c base(13) + cube + (isnot_0 or ... or isnot_12) + (not isnot_j, j=1..12)\n')
            f.write('p cnf %d %d\n' % (inst.cnf.nv, len(cl)))
            for c in cl:
                f.write(' '.join(map(str, c)) + ' 0\n')
        open(fn + '.emptyproof', 'w').close()
        r = subprocess.run([TOOL + '/third_party/bin/drat-trim', fn, fn + '.emptyproof'],
                           capture_output=True, text=True)
        v = [l for l in r.stdout.splitlines() if l.startswith('s ') or 'trivial' in l.lower()]
        print('coverage %s: unit propagation conflict %s; drat-trim (empty proof): %s' % (
            g, not st, v), flush=True)
        res &= (not st) and any(l.strip() == 's VERIFIED' for l in r.stdout.splitlines())
    return res


if __name__ == '__main__':
    out = sys.argv[1]
    t0 = time.time()
    G = automorphisms(7, FANO)
    print('Fano: |Aut| = %d, 2-transitive on points: %s' % (
        len(G), len({(p[0], p[1]) for p in G}) == 42), flush=True)
    allok = coverage(out)
    systems = [('K4 pairs', 4, [list(e) for e in itertools.combinations(range(4), 2)], 8),
               ('K5 pairs', 5, [list(e) for e in itertools.combinations(range(5), 2)], 10),
               ('4 choose 3', 4, [list(e) for e in itertools.combinations(range(4), 3)], 8),
               ('5 choose 4', 5, [list(e) for e in itertools.combinations(range(5), 4)], 9)]
    # (a first run also had '5 choose 3' (UNSAT up to 10, minimum not reached) and 'K6 pairs'
    #  (UNSAT up to 11, size 12 too slow); both dropped: they never reach a SAT size)
    for name, n, sets, smax in systems:
        allok &= check_system(name, n, sets, smax)
    # Fano at the SAT sizes 14, 15
    prob = Problem(Target.boolean_sums(7, FANO), Basis(1), 'nf', SB())
    for s in (14, 15):
        inst, _ = prob.encode(s)
        cs = {}
        for k in ('or_x0x1', 'and_x0x1', 'not_x0'):     # stop at the first SAT cube
            cs[k] = solve(inst.cnf.clauses, cubes(inst.meta)[k])
            if cs[k]:
                break
        print('Fano s=%d: cubes (tried in this order, stop at first SAT) %s' % (
            s, {k: int(v) for k, v in cs.items()}), flush=True)
        allok &= any(cs.values())
    print('VALIDATION split: all ok = %s (%.0fs)' % (allok, time.time() - t0), flush=True)
