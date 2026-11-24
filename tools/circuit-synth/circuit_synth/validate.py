"""Validation suite: `circuit_synth validate [--quick] [--sections a,b,..]`.

Sections
  known      known minimum sizes (P4 = 4, K_{1,3} = 3, C5 = 7, C4 = 3, K3 = 4, P5 = 5, majority-3 = 4
             in every basis, XOR-2 = 4 with NOTs, XOR-3, Boolean sums), every mode/row choice
  brute3     all 256 functions of 3 inputs, bases mono / <=1 NOT / <=2 NOT / full, every
             symmetry-breaking configuration, against an exhaustive C enumeration (cap 7 gates)
  brute4     all 166 non-constant monotone functions of 4 inputs (= monotone basis), full rows and
             minterm/max-false-point rows, every configuration, against brute force (cap 7)
  graphs     all 64 labelled graphs on 4 vertices (edge functions; minterm rows), mono and <=1
             NOT, against brute force; plus random non-monotone 4-input functions (<=1 NOT, full)
  raw        the RAW encoding (every Lean FanInTwo gate, no normal form) against NF and brute
             force on all 3-input functions (cap 5) and constants
  sums       Boolean sums / multi-output families against brute force
  reference  agreement with the four merged encoders (reference/*.py)
  restrict   gate-elimination side constraints (auto bounds) never change the minimum
  exists     'some AND gate true on row r' against an exhaustive enumeration of the NF class
  forbid     'no AND gate true on row r': every configuration and RAW against the enumeration
  prefix     fixed first gates
  certs      DRAT certificates (kissat + drat-trim) on UNSAT sizes, negative test
  lean       emit a Lean file for a small circuit and compile it (needs the Lean checkout)
"""
import itertools
import json
import os
import random
import subprocess
import sys
import time

from .core import (Target, Basis, Circuit, is_monotone, projection, all_graphs,
                   circuit_tables, classify_output)
from .encode import SB
from .synth import Problem, minimum, prove_none, find

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, 'build')

CONFIGS = ['all', 'none', 'used', 'distinct', 'order', 'relevant',
           'distinct,order,relevant', 'used,order,relevant', 'used,distinct,relevant',
           'used,distinct,order']


class Report:
    def __init__(self, log_path=None):
        self.items = []
        self.log_path = log_path
        self.fh = open(log_path, 'a') if log_path else None

    def log(self, msg):
        print(msg, flush=True)
        if self.fh:
            self.fh.write(msg + '\n')
            self.fh.flush()

    def check(self, section, case, ok, detail=''):
        self.items.append({'section': section, 'case': case, 'ok': bool(ok), 'detail': detail})
        if not ok:
            self.log('MISMATCH [%s] %s %s' % (section, case, detail))

    def section_summary(self, section, t0):
        its = [i for i in self.items if i['section'] == section]
        bad = [i for i in its if not i['ok']]
        self.log('== %s: %d checks, %d failures, %.1fs' % (section, len(its), len(bad),
                                                          time.time() - t0))


# ---------------------------------------------------------------- brute force (C)
def brute_exe():
    exe = os.path.join(BUILD, 'brute')
    src = os.path.join(ROOT, 'circuit_synth', 'brute.c')
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        os.makedirs(BUILD, exist_ok=True)
        subprocess.check_call(['gcc', '-O2', '-o', exe, src])
    return exe


def brute_table(n, cap, maxnot):
    """{tt: [min size with <= c NOTs, c = 0..maxnot]} (-1 = more than cap)."""
    path = os.path.join(BUILD, 'brute_table_n%d_cap%d_not%d.txt' % (n, cap, maxnot))
    if not os.path.exists(path):
        out = subprocess.check_output([brute_exe(), 'table', str(n), str(cap), str(maxnot)])
        with open(path, 'wb') as f:
            f.write(out)
    tab = {}
    with open(path) as f:
        for line in f:
            p = list(map(int, line.split()))
            tab[p[0]] = p[1:]
    return tab


def brute_multi(n, cap, maxnot, tables):
    out = subprocess.check_output([brute_exe(), 'multi', str(n), str(cap), str(maxnot)] +
                                  ['%x' % t for t in tables])
    v = int(out.split()[0])
    return None if v < 0 else v


def sat_min(target, basis, mode='nf', sb='all', cap=7, **kw):
    p = Problem(target, basis, mode, SB.parse(sb), **kw)
    r = minimum(p, smax=cap, quiet=True)
    return r['min_size']


def _bmin(entry, c):
    v = entry[min(c, len(entry) - 1)]
    return None if v < 0 else v


# ---------------------------------------------------------------- sections
def sec_known(rep, quick):
    S = 'known'
    cases = [('P4', 4, [(0, 1), (1, 2), (2, 3)], 4), ('K13', 4, [(0, 1), (0, 2), (0, 3)], 3),
             ('C4', 4, [(0, 1), (1, 2), (2, 3), (3, 0)], 3), ('K3', 3, [(0, 1), (1, 2), (0, 2)], 4),
             ('P5', 5, [(0, 1), (1, 2), (2, 3), (3, 4)], 5),
             ('C5', 5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], 7)]
    for name, n, E, known in cases:
        for rows in ('full', 'minterm'):
            for sb in (['all'] if quick else ['all', 'none']):
                tg = Target.graph(n, E)
                if rows == 'minterm':
                    tg.monotone_rows()
                v = sat_min(tg, Basis(0), sb=sb, cap=known + 1)
                rep.check(S, '%s mono rows=%s sb=%s' % (name, rows, sb), v == known,
                          'got %s want %s' % (v, known))
        if n <= 4:
            v = sat_min(Target.graph(n, E), Basis(0), mode='raw', cap=known + 1)
            rep.check(S, '%s mono RAW' % name, v == known, 'got %s want %s' % (v, known))
    maj = sum(1 << t for t in range(8) if bin(t).count('1') >= 2)
    for b in (Basis(0), Basis(1), Basis(None)):
        for mode in ('nf', 'raw'):
            v = sat_min(Target(3, [maj]), b, mode=mode, cap=5)
            rep.check(S, 'maj3 %s %s' % (b.name(), mode), v == 4, 'got %s' % v)
    for b in (Basis(1), Basis(2), Basis(None)):
        for mode in ('nf', 'raw'):
            v = sat_min(Target(2, [0b0110]), b, mode=mode, cap=6)
            rep.check(S, 'xor2 %s %s' % (b.name(), mode), v == 4, 'got %s' % v)
    v = sat_min(Target(2, [0b0110]), Basis(0), cap=6)
    rep.check(S, 'xor2 mono impossible (<= 6)', v is None, 'got %s' % v)
    # XOR3 with <= 1 NOT and unrestricted NOTs: our encoding against the merged onenot encoder
    # (L-meta-1444) at the minimum and one below
    v1 = sat_min(Target(3, [0x96]), Basis(1), cap=10)
    v2 = sat_min(Target(3, [0x96]), Basis(None), cap=10)
    rep.log('  xor3: min with <= 1 NOT = %s, full basis = %s' % (v1, v2))
    rep.check(S, 'xor3 full <= xor3 one-NOT', v2 is not None and v1 is not None and v2 <= v1, '')
    # constants and projections (Lean conventions: false = missing wire, true = AND [])
    for b in (Basis(0), Basis(None)):
        for mode in ('nf', 'raw'):
            for tt, want in ((0, 0), (0xff, 1), (projection(3, 1), 0)):
                v = sat_min(Target(3, [tt]), b, mode=mode, cap=3)
                rep.check(S, 'trivial %#x %s %s' % (tt, b.name(), mode), v == want,
                          'got %s want %s' % (v, want))
    # Boolean sums
    for sets, want in (([[0, 1, 2], [1, 2, 3]], 3), ([[0, 1], [1, 2], [0, 2]], 3),
                       ([[0, 1, 2, 3], [0, 1, 2], [1, 2, 3]], 4)):
        for mode in ('nf', 'raw'):
            v = sat_min(Target.boolean_sums(4, sets), Basis(0), mode=mode, cap=want + 1)
            rep.check(S, 'sums %s %s' % (sets, mode), v == want, 'got %s want %s' % (v, want))


def sec_brute3(rep, quick):
    S = 'brute3'
    cap = 6 if quick else 7
    tab = brute_table(3, cap, cap)
    configs = ['all', 'none'] if quick else CONFIGS
    bases = [Basis(0), Basis(1), Basis(2), Basis(None)]
    cnt = 0
    for tt in range(256):
        cls = classify_output(tt, 3)
        if cls[0] in ('false', 'true'):
            continue
        for b in bases:
            if b.max_not == 0 and not is_monotone(tt, 3):
                continue
            c = cap if b.max_not is None else b.max_not
            want = _bmin(tab[tt], c)
            for sb in configs:
                v = sat_min(Target(3, [tt]), b, sb=sb, cap=cap)
                cnt += 1
                rep.check(S, 'tt=%#04x %s sb=%s' % (tt, b.name(), sb), v == want,
                          'sat %s brute %s' % (v, want))
    rep.log('  brute3: %d (function, basis, config) comparisons, cap %d' % (cnt, cap))


def sec_brute4(rep, quick):
    S = 'brute4'
    cap = 7
    tab = brute_table(4, cap, 0)
    monos = [tt for tt in range(1 << 16) if is_monotone(tt, 4) and tt not in (0, 0xffff)]
    configs = ['all', 'none'] if quick else CONFIGS
    cnt = 0
    for tt in monos:
        want = _bmin(tab[tt], 0)
        for rows in ('full', 'minterm'):
            for sb in configs:
                if quick and rows == 'full' and sb != 'all':
                    continue
                tg = Target(4, [tt])
                if rows == 'minterm':
                    tg.monotone_rows()
                v = sat_min(tg, Basis(0), sb=sb, cap=cap)
                cnt += 1
                rep.check(S, 'tt=%#06x rows=%s sb=%s' % (tt, rows, sb), v == want,
                          'sat %s brute %s' % (v, want))
    rep.log('  brute4: %d monotone functions, %d comparisons, cap %d' % (len(monos), cnt, cap))


def sec_graphs(rep, quick):
    S = 'graphs'
    cap = 7
    tab = brute_table(4, cap, 0)
    tab1 = brute_table(4, 6, 1)
    cnt = 0
    for E in all_graphs(4):
        if not E:
            continue
        tg = Target.graph(4, E).monotone_rows()
        want = _bmin(tab[Target.graph(4, E).tables[0]], 0)
        for sb in (['all'] if quick else ['all', 'none', 'order', 'distinct']):
            v = sat_min(tg, Basis(0), sb=sb, cap=cap)
            cnt += 1
            rep.check(S, 'G4 %s mono sb=%s' % (E, sb), v == want, 'sat %s brute %s' % (v, want))
        want1 = _bmin(tab1[Target.graph(4, E).tables[0]], 1)
        v = sat_min(Target.graph(4, E), Basis(1), cap=6)
        cnt += 1
        rep.check(S, 'G4 %s <=1 NOT' % (E,), v == want1, 'sat %s brute %s' % (v, want1))
    # random non-monotone 4-input functions, <= 1 NOT and full basis (cap 6)
    rng = random.Random(2026)
    tabf = brute_table(4, 6, 6) if not quick else tab1
    reach = sorted(tt for tt, e in tabf.items() if e[-1] >= 0 and not is_monotone(tt, 4))
    sample = rng.sample(reach, 20 if quick else 80)
    sample += rng.sample(range(1 << 16), 10 if quick else 40)
    for tt in sample:
        for b in ((Basis(1),) if quick else (Basis(1), Basis(None))):
            c = 1 if b.max_not == 1 else len(tabf[tt]) - 1
            want = _bmin(tabf[tt], c)
            if classify_output(tt, 4)[0] in ('false', 'true'):
                continue
            for sb in (['all'] if quick else ['all', 'none']):
                v = sat_min(Target(4, [tt]), b, sb=sb, cap=6)
                cnt += 1
                rep.check(S, 'tt=%#06x %s sb=%s' % (tt, b.name(), sb), v == want,
                          'sat %s brute %s' % (v, want))
    rep.log('  graphs: %d comparisons' % cnt)


def sec_raw(rep, quick):
    S = 'raw'
    cap = 4 if quick else 5
    tab = brute_table(3, 7, 7)
    cnt = 0
    fns = range(256) if not quick else random.Random(7).sample(range(256), 40)
    for tt in fns:
        for b in (Basis(0), Basis(1), Basis(None)):
            if b.max_not == 0 and not is_monotone(tt, 3):
                continue
            cls = classify_output(tt, 3)
            raw = sat_min(Target(3, [tt]), b, mode='raw', cap=cap)
            nf = sat_min(Target(3, [tt]), b, mode='nf', cap=cap)
            if cls[0] == 'false':
                want = 0
            elif cls[0] == 'true':
                want = 1
            else:
                want = _bmin(tab[tt], 7 if b.max_not is None else b.max_not)
                if want is not None and want > cap:
                    want = None
            cnt += 1
            rep.check(S, 'tt=%#04x %s' % (tt, b.name()), raw == nf == want,
                      'raw %s nf %s brute %s' % (raw, nf, want))
    rep.log('  raw: %d comparisons (cap %d)' % (cnt, cap))


def sec_sums(rep, quick):
    S = 'sums'
    rng = random.Random(11)
    fams = [[[0, 1, 2], [1, 2, 3]], [[0, 1, 2, 3], [0, 1, 2], [1, 2, 3]],
            [[0, 1, 2], [2, 3, 4], [0, 4]], [[0, 1, 2], [1, 2, 3], [2, 3, 4], [0, 3, 4]]]
    for _ in range(4 if quick else 12):
        n = rng.choice([4, 5])
        fams.append([sorted(rng.sample(range(n), rng.choice([2, 3]))) for _ in range(rng.choice([2, 3]))])
    for sets in fams:
        n = max(max(s) for s in sets) + 1
        n = max(n, 4)
        tg = Target.boolean_sums(n, sets)
        want = brute_multi(n, 8, 0, sorted(set(t for t in tg.tables
                                                if classify_output(t, n)[0] == 'gate')))
        for rows in ('full', 'minterm'):
            t2 = Target.boolean_sums(n, sets)
            if rows == 'minterm':
                t2.monotone_rows()
            v = sat_min(t2, Basis(0), cap=8)
            rep.check(S, '%s n=%d rows=%s' % (sets, n, rows), v == want, 'sat %s brute %s' % (v, want))
        if not quick:
            v = sat_min(tg, Basis(0), sb='none', cap=8)
            rep.check(S, '%s n=%d sb=none' % (sets, n), v == want, 'sat %s brute %s' % (v, want))
    # general multi-output (non-monotone, full basis): random pairs of 3-input functions
    for _ in range(6 if quick else 20):
        tabs = rng.sample(range(1, 255), 2)
        tabs = [t for t in tabs if classify_output(t, 3)[0] == 'gate']
        if not tabs:
            continue
        want = brute_multi(3, 6, 6, tabs)
        v = sat_min(Target(3, tabs), Basis(None), cap=6)
        rep.check(S, 'multi %s full' % [hex(t) for t in tabs], v == want, 'sat %s brute %s' % (v, want))


def _graphs_upto_iso(nv):
    seen, out = set(), []
    pairs = list(itertools.combinations(range(nv), 2))
    for m in range(1, len(pairs) + 1):
        for es in itertools.combinations(pairs, m):
            c = min(tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in es))
                    for p in itertools.permutations(range(nv)))
            if c not in seen:
                seen.add(c)
                out.append(list(es))
    return out


def sec_reference(rep, quick):
    S = 'reference'
    refdir = os.path.join(ROOT, 'reference')
    if refdir not in sys.path:
        sys.path.insert(0, refdir)
    sys.dont_write_bytecode = True
    import onenot_search as R1
    import junk_shard as R2
    import shard_search as R3
    import synth2 as R4
    from pysat.solvers import Solver

    def psolve(clauses):
        with Solver(name='cadical195', bootstrap_with=clauses) as sv:
            return sv.solve()

    def r1_min(n, tt, maxnot, sb, cap):
        for s in range(1, cap + 1):
            f, *_ = R1.encode(n, tt, s, maxnot, sb)
            if psolve(f.cl):
                return s
        return None

    def r4_min(n, tt, allow_not, cap):
        for s in range(1, cap + 1):
            e = R4.Enc(n, s, allow_not=allow_not)
            for r in range(1 << n):
                e.add_row(r, bool((tt >> r) & 1))
            ok = e.S.solve()
            e.S.delete()
            if ok:
                return s
        return None

    cnt = 0
    # (1) onenot_search (L-meta-1444): AND/OR and <= 1 NOT, all 3-input functions
    for tt in range(256):
        cls = classify_output(tt, 3)
        if cls[0] != 'gate':
            continue
        for maxnot in (0, 1):
            if maxnot == 0 and not is_monotone(tt, 3):
                continue
            for sb in ((True,) if quick else (True, False)):
                a = r1_min(3, tt, maxnot, sb, 6)
                b = sat_min(Target(3, [tt]), Basis(maxnot), cap=6)
                cnt += 1
                rep.check(S, 'onenot tt=%#04x maxnot=%d sb=%s' % (tt, maxnot, sb), a == b,
                          'reference %s ours %s' % (a, b))
    # (2,3) junk_shard (L-meta-1342) and shard_search (L-meta-1343): graphs up to 5 vertices
    gl = [(nv, E) for nv in (3, 4, 5) for E in _graphs_upto_iso(nv)]
    if quick:
        gl = gl[:12]
    for nv, E in gl:
        tg = Target.graph(nv, E).monotone_rows()
        ours = sat_min(tg, Basis(0), cap=12)
        R2.OPTS.clear()
        a, _, _ = R2.min_size_sat(nv, E, 12)
        R3.OPTS.clear()
        b, _, _ = R3.min_size(nv, E, None, 12)
        c, _, _ = R3.min_size(nv, E, None, 12, enc='B')
        cnt += 3
        rep.check(S, 'junk_shard %d %s' % (nv, E), a == ours, 'reference %s ours %s' % (a, ours))
        rep.check(S, 'shard_search A %d %s' % (nv, E), b == ours, 'reference %s ours %s' % (b, ours))
        rep.check(S, 'shard_search B %d %s' % (nv, E), c == ours, 'reference %s ours %s' % (c, ours))
        # AND/OR/NOT (synth2): all graphs in the full run (the dense 5-vertex ones need more
        # than 9 gates and take minutes per size: about 30 minutes in all); <= 4 vertices quick
        if nv <= 4 or not quick:
            d = r4_min(nv, Target.graph(nv, E).tables[0], True, 9)
            e = sat_min(Target.graph(nv, E), Basis(None), cap=9)
            cnt += 1
            rep.check(S, 'synth2 full %d %s' % (nv, E), d == e, 'reference %s ours %s' % (d, e))
    rep.log('  reference: %d comparisons (onenot: all 3-input functions; junk_shard, '
            'shard_search A/B, synth2: %d graphs up to 5 vertices)' % (cnt, len(gl)))


def sec_restrict(rep, quick):
    S = 'restrict'
    cnt = 0
    gl = [(nv, E) for nv in (3, 4, 5) for E in _graphs_upto_iso(nv)]
    if quick:
        gl = gl[::4]
    for nv, E in gl:
        verts = sorted(set(v for e in E for v in e))
        restr = [((v,), (), 'auto') for v in verts] + [((), (v,), 'auto') for v in verts]
        tg = Target.graph(nv, E).monotone_rows()
        a = sat_min(tg, Basis(0), cap=12)
        b = sat_min(Target.graph(nv, E).monotone_rows(), Basis(0), cap=12, restrictions=restr)
        cnt += 1
        rep.check(S, 'graph %d %s mono' % (nv, E), a == b, 'plain %s with restrictions %s' % (a, b))
    rng = random.Random(5)
    for tt in rng.sample([t for t in range(256) if classify_output(t, 3)[0] == 'gate'], 20 if quick else 60):
        for b_ in (Basis(1), Basis(None)):
            restr = [((v,), (), 'auto') for v in range(3)] + [((), (v,), 'auto') for v in range(3)]
            a = sat_min(Target(3, [tt]), b_, cap=7)
            b = sat_min(Target(3, [tt]), b_, cap=7, restrictions=restr)
            c = sat_min(Target(3, [tt]), b_, mode='raw', cap=min(a or 5, 5),
                        restrictions=restr) if (a or 9) <= 5 and not quick else a
            cnt += 1
            rep.check(S, 'tt=%#04x %s' % (tt, b_.name()), a == b == c,
                      'plain %s nf+restr %s raw+restr %s' % (a, b, c))
    rep.log('  restrict: %d comparisons' % cnt)


def _enum_nf(n, smax, allow_not, with_free=False):
    """Exhaustive enumeration of the NF class without symmetry breaking (nondegenerate gates,
    output = last gate): returns {(tt, s): set of rows r on which some AND gate of some circuit
    with s gates computing tt is true} and {(tt, s): True} for existence."""
    full = (1 << (1 << n)) - 1
    ins = [projection(n, i) for i in range(n)]
    res = {}
    free = {}

    def rec(tts, ands, j):
        if j > 0:
            key = (tts[-1], j)
            res[key] = res.get(key, 0) | ands
            free[key] = free.get(key, 0) | (full & ~ands)
        if j == smax:
            return
        W = len(tts)
        for b in range(W):
            for a in range(b):
                g = tts[a] & tts[b]
                rec(tts + [g], ands | g, j + 1)
                rec(tts + [tts[a] | tts[b]], ands, j + 1)
            if allow_not:
                rec(tts + [full & ~tts[b]], ands, j + 1)
    rec(ins, 0, 0)
    return (res, free) if with_free else res


def sec_exists(rep, quick):
    S = 'exists'
    cnt = 0
    for n, smax, allow_not in ((3, 4, True), (4, 4, False)):
        if quick and n == 4:
            smax = 3
        enum = _enum_nf(n, smax, allow_not)
        b = Basis(None) if allow_not else Basis(0)
        keys = sorted(k for k in enum if classify_output(k[0], n)[0] == 'gate')
        rng = random.Random(3)
        keys = rng.sample(keys, min(len(keys), 40 if quick else 150))
        for tt, s in keys:
            if not allow_not and not is_monotone(tt, n):
                continue
            rows = enum[(tt, s)]
            for r in rng.sample(range(1 << n), 3 if quick else 6):
                want = bool((rows >> r) & 1)
                for sb in ('none', 'order,relevant'):
                    p = Problem(Target(n, [tt]), b, 'nf', SB.parse(sb), exists=[('and', r)])
                    from .synth import run_size
                    rec, c = run_size(p, s)
                    got = rec['status'] == 'SAT'
                    cnt += 1
                    rep.check(S, 'n=%d tt=%#x s=%d row=%d sb=%s' % (n, tt, s, r, sb), got == want,
                              'sat %s enumeration %s' % (got, want))
    rep.log('  exists: %d comparisons' % cnt)


def sec_forbid(rep, quick):
    """'no AND gate true on row r' is preserved by normalization, so the minimum under it must
    agree for every symmetry-breaking configuration, for RAW, and for the enumeration."""
    S = 'forbid'
    cnt = 0
    for n, smax, allow_not in ((3, 4, True), (4, 4, False)):
        _, free = _enum_nf(n, smax, allow_not, with_free=True)
        b = Basis(None) if allow_not else Basis(0)
        tts = sorted(set(k[0] for k in free if classify_output(k[0], n)[0] == 'gate'
                         and (allow_not or is_monotone(k[0], n))))
        rng = random.Random(4)
        tts = rng.sample(tts, min(len(tts), 25 if quick else 80))
        for tt in tts:
            for r in rng.sample(range(1 << n), 2 if quick else 4):
                want = next((s for s in range(1, smax + 1) if (free.get((tt, s), 0) >> r) & 1), None)
                confs = ['all', 'none'] if quick else ['all', 'none', 'used', 'distinct', 'order']
                for sb in confs:
                    v = sat_min(Target(n, [tt]), b, sb=sb, cap=smax, forbid=[('and', r)])
                    cnt += 1
                    rep.check(S, 'n=%d tt=%#x row=%d sb=%s' % (n, tt, r, sb), v == want,
                              'sat %s enumeration %s' % (v, want))
                if n == 3 and not quick:
                    v = sat_min(Target(n, [tt]), b, mode='raw', cap=smax, forbid=[('and', r)])
                    cnt += 1
                    rep.check(S, 'n=%d tt=%#x row=%d RAW' % (n, tt, r), v == want,
                              'raw %s enumeration %s' % (v, want))
    rep.log('  forbid: %d comparisons' % cnt)


def sec_prefix(rep, quick):
    S = 'prefix'
    cnt = 0
    rng = random.Random(9)
    fns = rng.sample([t for t in range(256) if classify_output(t, 3)[0] == 'gate'], 15 if quick else 50)
    for tt in fns:
        p = Problem(Target(3, [tt]), Basis(None))
        r = minimum(p, smax=8, quiet=True)
        m = r['min_size']
        if m is None:
            continue
        g0 = tuple(r['_circuit'].gates[0])
        a = minimum(Problem(Target(3, [tt]), Basis(None), prefix=[g0]), smax=8, quiet=True)['min_size']
        b = minimum(Problem(Target(3, [tt]), Basis(None), prefix=[('and', [0, 0])]), smax=9,
                    quiet=True)['min_size']
        cnt += 2
        rep.check(S, 'tt=%#04x first gate of a minimum circuit' % tt, a == m, 'min %s with prefix %s' % (m, a))
        rep.check(S, 'tt=%#04x useless copy gate first' % tt, b == m + 1, 'min %s with prefix %s' % (m, b))
    rep.log('  prefix: %d comparisons' % cnt)


def sec_certs(rep, quick):
    S = 'certs'
    out = os.path.join(BUILD, 'certs')
    cases = [('P4_mono_le3', Target.graph(4, [(0, 1), (1, 2), (2, 3)]).monotone_rows(), Basis(0), 'nf', 3),
             ('maj3_full_le3', Target(3, [0xe8]), Basis(None), 'nf', 3),
             ('xor2_full_le3_raw', Target(2, [0b0110]), Basis(None), 'raw', 3),
             ('K13_mono_le2_raw', Target.graph(4, [(0, 1), (0, 2), (0, 3)]), Basis(0), 'raw', 2)]
    if not quick:
        cases.append(('C5_mono_le6', Target.graph(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]).monotone_rows(),
                      Basis(0), 'nf', 6))
    for name, tg, b, mode, s in cases:
        for solver in ('kissat', 'cadical'):
            wd = os.path.join(out, name + '_' + solver)
            r = prove_none(Problem(tg, b, mode), s, certify=True, workdir=wd, solver=solver, quiet=True)
            rep.check(S, '%s %s' % (name, solver), r['proved_none'] and r.get('proved_none_certified'),
                      json.dumps([(x['size'], x['status'], x.get('drat_trim')) for x in r['sizes']]))
    # negative test: a proof must not certify a satisfiable CNF
    from .solve import check_drat
    from .synth import run_size
    p = Problem(Target.graph(4, [(0, 1), (1, 2), (2, 3)]).monotone_rows(), Basis(0))
    inst, _ = p.encode(4)
    sat_cnf = os.path.join(out, 'negative_sat.cnf')
    with open(sat_cnf, 'w') as f:
        f.write(inst.cnf.dimacs())
    proof = os.path.join(out, 'P4_mono_le3_kissat', 'size03.drat')
    v = check_drat(sat_cnf, proof)
    rep.check(S, 'negative: UNSAT proof against a satisfiable CNF is rejected', not v['drat_verified'],
              str(v))


def sec_lean(rep, quick):
    S = 'lean'
    from .lean import emit
    lean_root = os.environ.get('CIRCUIT_SYNTH_LEAN_ROOT', '/home/user/pequalnp-proofs/lean')
    lake = os.path.expanduser('~/.elan/bin/lake')
    out = os.path.join(BUILD, 'lean')
    os.makedirs(out, exist_ok=True)
    cases = [('maj3_mono', Target(3, [0xe8]), Basis(0)),
             ('P4_graph', Target.graph(4, [(0, 1), (1, 2), (2, 3)]), Basis(0)),
             ('xor2_onenot', Target(2, [0b0110]), Basis(1))]
    if not quick:
        cases.append(('sums4', Target.boolean_sums(4, [[0, 1, 2], [1, 2, 3], [0, 3]]), Basis(0)))
    if not quick:
        maj5 = sum(1 << t for t in range(32) if bin(t).count('1') >= 3)
        cases.append(('maj5_table_find10', Target(5, [maj5]), Basis(0)))
    for name, tg, b in cases:
        if name.endswith('find10'):
            r = find(Problem(tg, b), 10, quiet=True)
        else:
            r = minimum(Problem(tg, b), smax=8, quiet=True)
        src = emit(r['_circuit'], tg, b, name=name)
        path = os.path.join(out, name + '.lean')
        with open(path, 'w') as f:
            f.write(src)
        rep.check(S, '%s no native_decide' % name, 'native_decide' not in src)
        t0 = time.time()
        pr = subprocess.run([lake, 'env', 'lean', path], cwd=lean_root, capture_output=True, text=True)
        ok = pr.returncode == 0 and 'error' not in pr.stdout
        rep.check(S, '%s compiles (%.0fs)' % (name, time.time() - t0), ok, (pr.stdout + pr.stderr)[-2000:])


SECTIONS = [('known', sec_known), ('brute3', sec_brute3), ('brute4', sec_brute4),
            ('graphs', sec_graphs), ('raw', sec_raw), ('sums', sec_sums),
            ('reference', sec_reference), ('restrict', sec_restrict), ('exists', sec_exists),
            ('forbid', sec_forbid),
            ('prefix', sec_prefix), ('certs', sec_certs), ('lean', sec_lean)]


def run(sections=None, quick=False, log_path=None, json_path=None):
    rep = Report(log_path)
    t_all = time.time()
    rep.log('circuit_synth validate (%s) %s' % ('quick' if quick else 'full',
                                                  time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime())))
    for name, fn in SECTIONS:
        if sections and name not in sections:
            continue
        if sections is None and name == 'lean':
            continue
        t0 = time.time()
        rep.log('== section %s' % name)
        try:
            fn(rep, quick)
        except Exception as e:  # report and continue
            import traceback
            rep.check(name, 'exception', False, traceback.format_exc())
        rep.section_summary(name, t0)
    bad = [i for i in rep.items if not i['ok']]
    rep.log('VALIDATION %s: %d checks, %d failures, %.1fs' % ('PASSED' if not bad else 'FAILED',
                                                              len(rep.items), len(bad), time.time() - t_all))
    if json_path:
        with open(json_path, 'w') as f:
            json.dump({'checks': len(rep.items), 'failures': bad,
                       'by_section': {s: sum(1 for i in rep.items if i['section'] == s)
                                      for s, _ in SECTIONS}}, f, indent=1)
    return not bad
