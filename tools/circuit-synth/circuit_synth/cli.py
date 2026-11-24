"""Command line interface. Run `circuit_synth -h` or see README.md."""
import argparse
import json
import os
import sys

from .core import Target, Basis, Circuit
from .encode import SB
from .synth import Problem, minimum, find, prove_none, run_size, VERSION


def parse_rowset(s, n):
    """'0b0101' / '0x5' / '5' (row index) or '{0,2}' (set of true variables)."""
    s = s.strip()
    if s.startswith('{'):
        vs = [int(x) for x in s.strip('{}').split(',') if x.strip()]
        return sum(1 << i for i in vs)
    return int(s, 0)


def build_target(a):
    if a.tt:
        assert a.n is not None, '--n is required with --tt'
        return Target.truth_table(a.n, a.tt, a.name)
    if a.tables:
        assert a.n is not None
        return Target.multi(a.n, [int(x, 0) for x in a.tables.split(',')])
    if a.graph is not None:
        E = [tuple(int(v) for v in e.split('-')) for e in a.graph.split(',') if e]
        n = a.n if a.n is not None else max(max(e) for e in E) + 1
        return Target.graph(n, E, a.name)
    if a.sums:
        sets = [[int(v) for v in S.split(',') if v] for S in a.sums.split(';')]
        n = a.n if a.n is not None else max(max(S) for S in sets if S) + 1
        return Target.boolean_sums(n, sets)
    if a.minterms:
        terms = [[int(v) for v in S.split(',') if v] for S in a.minterms.split(';')]
        mf = None
        if a.maxfalse:
            mf = [[int(v) for v in S.split(',') if v] for S in a.maxfalse.split(';')]
        n = a.n if a.n is not None else max(max(S) for S in terms if S) + 1
        return Target.monotone_from_minterms(n, terms, mf, a.name)
    raise SystemExit('give a target: --tt, --tables, --graph, --sums or --minterms')


def build_problem(a):
    tg = build_target(a)
    basis = Basis.parse(a.basis)
    rows = a.rows
    if rows == 'auto':
        rows = 'minterm' if basis.max_not == 0 and tg.monotone() and (a.graph or a.minterms or a.sums) else 'full'
    if rows == 'minterm':
        tg.monotone_rows()
    prefix = []
    if a.prefix:
        for g in a.prefix.split(';'):
            op, _, ins = g.partition(':')
            prefix.append((op.strip(), [int(x) for x in ins.split(',') if x.strip()]))
    exists = []
    for e in a.exists or []:
        op, _, row = e.partition('@')
        exists.append((op.strip(), parse_rowset(row, tg.n)))
    forbid = []
    for e in a.forbid or []:
        op, _, row = e.partition('@')
        forbid.append((op.strip(), parse_rowset(row, tg.n)))
    restr = []
    for r in a.restrict or []:
        d = {'P': '', 'Q': '', 'L': 'auto'}
        for part in r.split(';'):
            k, _, v = part.partition('=')
            d[k.strip()] = v.strip()
        P = [int(x) for x in d['P'].split(',') if x]
        Q = [int(x) for x in d['Q'].split(',') if x]
        restr.append((P, Q, d['L'] if d['L'] == 'auto' else int(d['L'])))
    return Problem(tg, basis, a.mode, SB.parse(a.sb), prefix, exists, restr, backend=a.backend,
                   forbid=forbid)


def report(res, a, prob):
    c = res.get('_circuit')
    pub = {k: v for k, v in res.items() if not k.startswith('_')}
    if a.json:
        print(json.dumps(pub, indent=1, default=list))
    else:
        for k in ('query', 'min_size', 'found', 'proved_none', 'proved_none_certified',
                  'all_unsat_certified'):
            if pub.get(k) is not None:
                print('%s: %s' % (k, pub[k]))
        if c is not None:
            print('circuit (%d gates):' % c.size)
            print(c.pretty())
            ver = [r for r in res['sizes'] if r.get('status') == 'SAT'][-1].get('verification')
            print('verification (Lean semantics, all %d inputs): %s' % (1 << c.n, ver))
    if c is not None and a.lean:
        from .lean import emit
        with open(a.lean, 'w') as f:
            f.write(emit(c, prob.target, prob.basis, name=a.name or 'Synth'))
        print('Lean file written: %s' % a.lean)


_TMPDIRS = []


def _plain(path, name):
    """The file `name` in the bundle, decompressing `name.xz` into a temporary file."""
    p = os.path.join(path, name)
    if os.path.exists(p):
        return p
    import lzma
    import tempfile
    from .solve import tmp_dir
    d = tempfile.mkdtemp(prefix='csynth_recheck_', dir=tmp_dir())
    _TMPDIRS.append(d)
    out = os.path.join(d, name)
    with lzma.open(p + '.xz') as fi, open(out, 'wb') as fo:
        fo.write(fi.read())
    return out


def cmd_recheck(path):
    """Re-generate every CNF of a bundle from its recorded spec, compare SHA-256, and re-run
    drat-trim on the stored proofs."""
    from .solve import check_drat, sha256_file
    with open(os.path.join(path, 'bundle.json')) as f:
        b = json.load(f)
    t = b['target']
    tg = Target(t['n'], [int(x, 16) for x in t['tables']])
    if t['row_mode'] == 'monotone':
        tg.monotone_rows()
    prob = Problem(tg, Basis.parse(b['basis']), b['mode'],
                   SB.parse(b['sb']) if b['mode'] == 'nf' else None,
                   [tuple(g) for g in b['prefix']], [tuple(e) for e in b['exists']],
                   [(set(P), set(Q), L) for P, Q, L in b['restrictions']],
                   forbid=[tuple(e) for e in b.get('forbid', [])])
    ok = True
    missing = []
    for r in b['sizes']:
        if 'cnf_sha256' not in r:
            print('size %d: %s (%s)' % (r['size'], r['status'], r.get('reason', 'no CNF stored')))
            continue
        inst, _ = prob.encode(r['size'])
        import hashlib
        comments = ['circuit_synth %s' % b['tool'].split()[-1], json.dumps(prob.spec()),
                    'size %d' % r['size']]
        h = hashlib.sha256(inst.cnf.dimacs(comments).encode()).hexdigest()
        same = h == r['cnf_sha256']
        line = 'size %d: %s, regenerated CNF sha256 %s' % (r['size'], r['status'],
                                                           'matches' if same else 'DIFFERS')
        ok &= same
        if r['status'] == 'UNSAT':
            cnf = _plain(path, os.path.basename(r['cnf']))
            pname = os.path.join(path, os.path.basename(r['proof']))
            if not (os.path.exists(pname) or os.path.exists(pname + '.xz')):
                print(line + ', proof not stored (sha256 %s...): re-run the solver to regenerate'
                      % r['proof_sha256'][:16])
                missing.append(r['size'])
                continue
            prf = _plain(path, os.path.basename(r['proof']))
            same_p = sha256_file(prf) == r['proof_sha256']
            same_c = sha256_file(cnf) == r['cnf_sha256']
            ok &= same_c
            v = check_drat(cnf, prf)
            line += ', proof sha256 %s, drat-trim: %s' % ('matches' if same_p else 'DIFFERS', v['drat_trim'])
            ok &= same_p and v['drat_verified']
        print(line)
    import shutil
    for d in _TMPDIRS:
        shutil.rmtree(d, ignore_errors=True)
    for sub in sorted(os.listdir(path)):          # sub-bundles of L=auto restriction bounds
        sp = os.path.join(path, sub)
        if os.path.isdir(sp) and os.path.exists(os.path.join(sp, 'bundle.json')):
            print('-- sub-bundle %s' % sub)
            ok &= cmd_recheck(sp)
    verdict = 'FAILED' if not ok else ('OK except sizes %s (proof not stored)' % missing
                                       if missing else 'OK')
    print('recheck %s: %s' % (path, verdict))
    return ok


def main(argv=None):
    ap = argparse.ArgumentParser(prog='circuit_synth', description=__doc__)
    ap.add_argument('command', choices=['min', 'find', 'none', 'validate', 'recheck', 'dimacs'])
    ap.add_argument('arg', nargs='?', help='bundle directory (recheck) / output file (dimacs)')
    g = ap.add_argument_group('target')
    g.add_argument('--n', type=int)
    g.add_argument('--tt', help='truth table: 0x.., 0b.., or 2^n characters 0/1 (row t: x_i = bit i of t)')
    g.add_argument('--tables', help='multi-output: comma separated truth tables')
    g.add_argument('--graph', help='edge list "0-1,1-2,..." (edge function)')
    g.add_argument('--sums', help='Boolean sums "0,1,2;1,2,3" (one OR per output)')
    g.add_argument('--minterms', help='monotone target "0,1;1,2" (one minterm per group)')
    g.add_argument('--maxfalse', help='optional check: the maximal false points "0,2;1,3"')
    g.add_argument('--name', default='f')
    g = ap.add_argument_group('class')
    g.add_argument('--basis', default='full', help='mono | full | knot=K (default full)')
    g.add_argument('--rows', default='auto', choices=['auto', 'full', 'minterm'])
    g.add_argument('--mode', default='nf', choices=['nf', 'raw'])
    g.add_argument('--sb', default='all', help='all | none | comma list of used,distinct,order,relevant')
    g.add_argument('--prefix', help='fixed first gates "and:0,1;or:2,4"')
    g.add_argument('--exists', action='append', help='OP@ROW: some OP gate is true on ROW ({0,2} or 0b101)')
    g.add_argument('--forbid', action='append', help='OP@ROW: no OP gate is true on ROW')
    g.add_argument('--restrict', action='append', help='"P=0,1;Q=3;L=auto|int" gate-elimination bound')
    g = ap.add_argument_group('run')
    g.add_argument('--size', type=int, help='size bound for find / none / dimacs')
    g.add_argument('--smax', type=int, default=30, help='largest size tried by min')
    g.add_argument('--certify', action='store_true', help='DRAT proofs + drat-trim for UNSAT sizes')
    g.add_argument('--solver', default='kissat', choices=['kissat', 'cadical'])
    g.add_argument('--backend', default='auto', choices=['auto', 'pysat', 'kissat', 'cadical'])
    g.add_argument('--timeout', type=int)
    g.add_argument('--out', help='certificate bundle directory (CNFs, proofs, bundle.json)')
    g.add_argument('--lean', help='write a Lean certificate file for the circuit found')
    g.add_argument('--json', action='store_true')
    g.add_argument('--quick', action='store_true', help='validate: reduced suite')
    g.add_argument('--sections', help='validate: comma separated section names')
    a = ap.parse_args(argv)

    if a.command == 'validate':
        from . import validate
        secs = a.sections.split(',') if a.sections else None
        os.makedirs(os.path.join(validate.BUILD), exist_ok=True)
        ok = validate.run(secs, a.quick, log_path=a.out and os.path.join(a.out, 'validate.log'),
                          json_path=a.out and os.path.join(a.out, 'validate.json'))
        return 0 if ok else 1
    if a.command == 'recheck':
        return 0 if cmd_recheck(a.arg) else 1
    prob = build_problem(a)
    if a.out:
        os.makedirs(a.out, exist_ok=True)
    if a.command == 'dimacs':
        inst, why = prob.encode(a.size)
        if inst is None:
            print(why)
            return 1
        with open(a.arg, 'w') as f:
            f.write(inst.cnf.dimacs([json.dumps(prob.spec()), 'size %d' % a.size]))
        print('wrote %s: %d vars, %d clauses' % (a.arg, inst.cnf.nv, len(inst.cnf.clauses)))
        return 0
    kw = dict(certify=a.certify, workdir=a.out, solver=a.solver, timeout=a.timeout, quiet=a.json)
    if a.command == 'min':
        res = minimum(prob, smax=a.smax, **kw)
    elif a.command == 'find':
        res = find(prob, a.size, **kw)
    else:
        kw['certify'] = True if a.certify or a.out else a.certify
        res = prove_none(prob, a.size, **kw)
    report(res, a, prob)
    return 0


if __name__ == '__main__':
    sys.exit(main())
