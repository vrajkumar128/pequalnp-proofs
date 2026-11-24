"""Order-3 K-local cases with one deficit flag fixed (refinement of L-meta-957 notes).

Setting (L-meta-957): K = set of k lines of PG(2,3) (orbit representative under PGL(3,3));
lines outside K are private 3-gate OR trees; every OR of 2, 3 or 4 points of a line outside K
is offered as a free 'library' wire; 3k - 1 free gates with at most one NOT must compute the
k line-ORs of K. UNSAT => no 38-gate one-NOT list keeps the 13 - k lines outside K as
private plain OR trees (for K in that orbit).

Refinement (this script): by the family bound applied to the free gates (see CERTIFICATE.md /
order3/README.md), every circuit of the relaxation that is correct on the rows e_u, m_w has at
least two deficit flags (w, u), w in K. Stab(K) acts on the 4k flags of K; one case per flag
orbit, with the orbit representative forced to be a deficit flag (+ at least 2 flags in all).
Soundness of fixing the flag needs the row set R to be Stab(K)-invariant: R starts as
{0, units, pairs, line indicators and complements} (PGL-invariant) and every counterexample
row is added together with its Stab(K)-orbit.

usage: kloc5.py K FLAGMODE [--s S] [--seed N]
  K        e.g. 0-1-2-3-7
  FLAGMODE 'orbits' (print flag orbits), 'i,u' (fix flag: index i into K, point u),
           'none2' (no fixed flag, at least two deficit flags), 'plain' (no deficit constraint)
"""
import argparse
import hashlib
import itertools
import random
import sys
import time

L957 = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-957'
sys.path.insert(0, L957)
import search957 as S  # noqa: E402


def stabilizer(G, K):
    out = []
    Ks = set(K)
    for g in G:
        lp = S.line_perm(g)
        if set(lp[w] for w in K) == Ks:
            out.append((g, lp))
    return out


def flag_orbits(stab, K):
    flags = [(i, u) for i, w in enumerate(K) for u in S.LINES[w]]
    seen, orbs = set(), []
    for f in flags:
        if f in seen:
            continue
        orb = set()
        for g, lp in stab:
            i, u = f
            orb.add((K.index(lp[K[i]]), g[u]))
        seen |= orb
        orbs.append((f, sorted(orb)))
    return orbs


def perm_row(t, g):
    r = 0
    for i in range(13):
        if (t >> i) & 1:
            r |= 1 << g[i]
    return r


def flags_of(gates, outs, lib, Kl):
    W1 = S.bit_wires_lib(13, lib, S.c01(gates, 1))
    W0 = S.bit_wires_lib(13, lib, S.c01(gates, 0))
    full = (1 << 13) - 1
    res = []
    for w, L in enumerate(Kl):
        m = full & ~sum(1 << i for i in L)
        if (W1[outs[w]] >> m) & 1:
            for u in L:
                if not ((W0[outs[w]] >> (1 << u)) & 1):
                    res.append((w, u))
    return res


KISSAT = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth/third_party/bin/kissat'


def _rec_add(self, cl):
    """Enc.add that also records the clause (for the --kissat first iteration)."""
    out = []
    for l in cl:
        if l is True:
            return
        if l is False:
            continue
        out.append(l)
    self.S.add_clause(out)
    self.nclauses += 1
    if not hasattr(self, '_rec'):
        self._rec = []
    self._rec.append(out)


def run(K, mode, s, seed, log, G=None, notpos=None, kissat=False, cnfdir=None):
    G = G or S.collineations()
    stab = stabilizer(G, K)
    lib, names = S.library(K)
    tabs = [S.ALL13[w] for w in K]
    Kl = [S.LINES[w] for w in K]
    log('K=%s |Stab(K)|=%d free gates %d library %d wires mode %s notpos %s' % (
        K, len(stab), s, len(lib), mode, notpos))
    if mode == 'orbits':
        for f, orb in flag_orbits(stab, K):
            log('  flag orbit rep %s size %d: %s' % (f, len(orb), orb))
        return None
    flag = None
    ex = None
    if mode == 'none2':
        ex = S.deficit_constraints(Kl, flag=None, min_total=2)
    elif mode != 'plain':
        flag = tuple(int(x) for x in mode.split(','))
        ex = S.deficit_constraints(Kl, flag=flag, min_total=2)
    rng = random.Random(seed)
    t0 = time.time()
    ex0 = ex

    def ex(E):
        # NOT-position split (propositional): notpos = 'none' -> no NOT gate; p -> gate p is NOT
        if ex0:
            ex0(E)
        if notpos == 'none':
            for j in range(s):
                E.add([-E.isnot[j]])
        elif notpos is not None:
            E.add([E.isnot[int(notpos)]])
    E = S.Enc(13, tabs, s, 1, extra=ex, lib=lib)
    rows = S.initial_rows(13, S.LINES)          # no random rows: PGL-invariant
    for g, lp in stab:
        assert set(perm_row(t, g) for t in rows) == rows
    for t in sorted(rows):
        E.add_row(t)
    log('  enc: s=%d rows=%d vars=%d clauses=%d build %.1fs' % (s, len(E.rows), E.nv, E.nclauses,
                                                                 time.time() - t0))
    it = 0
    while True:
        it += 1
        assum = E.post_distinct()
        ts = time.time()
        if kissat and it == 1:
            # iteration 1 with kissat on the recorded clauses (+ the activation unit)
            import os
            import subprocess
            fn = os.path.join(cnfdir or '.', 'iter1_%s_%s_%s.cnf' % (
                '-'.join(map(str, K)), mode.replace(',', '-'), notpos))
            with open(fn, 'w') as f:
                f.write('p cnf %d %d\n' % (E.nv, len(E._rec) + len(assum)))
                for c in E._rec:
                    f.write(' '.join(map(str, c)) + ' 0\n')
                for a_ in assum:
                    f.write('%d 0\n' % a_)
            r = subprocess.run([KISSAT, '-q', fn], capture_output=True, text=True)
            st = [l for l in r.stdout.splitlines() if l.startswith('s ')]
            log('  iter 1 (kissat, CNF %d vars %d clauses): %s %.1fs' % (
                E.nv, len(E._rec) + 1, st[0] if st else 'rc %d' % r.returncode, time.time() - ts))
            os.remove(fn)
            if st and st[0] == 's UNSATISFIABLE':
                log('RESULT K=%s mode=%s notpos=%s s=%d -> UNSAT (1 iterations, %d rows, kissat, %.1fs)'
                    % (K, mode, notpos, s, len(E.rows), time.time() - t0))
                return 'UNSAT'
            log('  kissat did not refute iteration 1; continuing with CaDiCaL CEGIS')
        res = E.S.solve(assumptions=assum)
        dt = time.time() - ts
        if res is False:
            log('  iter %d: UNSAT %.1fs (rows %d) total %.1fs' % (it, dt, len(E.rows), time.time() - t0))
            log('RESULT K=%s mode=%s notpos=%s s=%d -> UNSAT (%d iterations, %d rows, %.1fs)' % (
                K, mode, notpos, s, it, len(E.rows), time.time() - t0))
            return 'UNSAT'
        gates, outs = E.decode(E.S.get_model())
        bad = S.check_all(13, tabs, gates, outs, 1, lib)
        if not bad:
            fl = flags_of(gates, outs, lib, Kl)
            log('  iter %d: SAT %.1fs VERIFIED on all 8192 inputs; deficit flags %s' % (it, dt, fl))
            if flag is not None:
                assert flag in fl and len(fl) >= 2, 'flag constraint not realized: encoding bug'
            log('RESULT K=%s mode=%s notpos=%s s=%d -> SAT circuit %s outs %s' % (
                K, mode, notpos, s, gates, outs))
            return 'SAT'
        new = S.pick_cex(13, bad, 2, rng)
        add = set()
        for t in new:
            add |= set(perm_row(t, g) for g, lp in stab)
        add -= set(E.rows)
        assert add
        for t in sorted(add):
            E.add_row(t)
        log('  iter %d: SAT %.1fs, %d wrong outputs, +%d rows (Stab-orbits) -> %d' % (
            it, dt, len(bad), len(add), len(E.rows)))


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('K')
    ap.add_argument('mode')
    ap.add_argument('--s', type=int, default=None)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--notpos', default=None, help="'none' or a gate position p (NOT at p)")
    ap.add_argument('--kissat', action='store_true', help='iteration 1 with kissat')
    a = ap.parse_args()
    K = tuple(int(x) for x in a.K.split('-'))
    s = a.s if a.s is not None else 3 * len(K) - 1
    lg = lambda m: print(m, flush=True)
    lg('search957.py sha256 %s' % hashlib.sha256(open(L957 + '/search957.py', 'rb').read()).hexdigest())
    if a.kissat:
        S.Enc.add = _rec_add
    run(K, a.mode, s, a.seed, lg, notpos=a.notpos, kissat=a.kissat)
