"""Driver: find / prove-none / minimum, with verification and certificates."""
import json
import os
import time

from .core import Circuit, Basis, Target, classify_output, circuit_tables, depends_on, lean_wires
from .encode import SB, encode_nf, encode_raw, decode, prefix_eliminable, subcube
from .solve import solve, solve_external

VERSION = '1.0'


class Problem:
    """target: core.Target; basis: core.Basis; mode: 'nf' or 'raw'.
    prefix: fixed first gates [(op, [inputs])] (NF only).
    exists: [(op, row)]: some gate with that op is true on input row `row`.
    forbid: [(op, row)]: no gate with that op is true on input row `row`.
    restrictions: [(P, Q, L)]: under x_P = 1, x_Q = 0 at most s - L gates have a constant
    input; L an int, or 'auto' (= minimum size of the restricted function, computed here)."""

    def __init__(self, target, basis, mode='nf', sb=None, prefix=(), exists=(), restrictions=(),
                 backend='auto', forbid=()):
        self.target, self.basis, self.mode = target, basis, mode
        self.sb = sb or SB()
        self.prefix = [(op, list(ins)) for op, ins in prefix]
        self.exists = list(exists)
        self.forbid = list(forbid)
        self.restrictions = list(restrictions)
        self.backend = backend
        self.sub_results = []
        if mode == 'raw' and self.prefix:
            raise ValueError('fixed prefix gates are supported in NF mode only')
        if self.target.row_mode == 'monotone' and self.basis.max_not != 0:
            raise ValueError('minterm/max-false-point rows are sound only for the monotone basis')
        pc = Circuit(target.n, self.prefix, [])
        if self.prefix and not self.basis.check(pc):
            raise ValueError('prefix gates are not in the basis')
        if mode == 'nf' and (self.exists or self.forbid) and any(
                classify_output(t, target.n)[0] == 'true' for t in target.tables):
            # the appended AND [] gate of a constant-true output is outside the NF class
            raise ValueError('a constant-true output with --exists/--forbid: use --mode raw')

    def describe(self):
        return {'target': self.target.to_json(), 'basis': self.basis.name(), 'mode': self.mode,
                'sb': self.sb.name() if self.mode == 'nf' else 'none (raw)',
                'prefix': self.prefix, 'exists': self.exists, 'forbid': self.forbid,
                'restrictions': [[sorted(P), sorted(Q), L] for P, Q, L in self.resolved_restrictions()]}

    def spec(self):
        """Canonical description written into every CNF header (recheck regenerates it)."""
        t = self.target
        return {'n': t.n, 'tables': [hex(x) for x in t.tables], 'row_mode': t.row_mode,
                'basis': self.basis.name(), 'mode': self.mode,
                'sb': self.sb.name() if self.mode == 'nf' else 'none (raw)',
                'prefix': self.prefix, 'exists': self.exists, 'forbid': self.forbid,
                'restrictions': [[sorted(P), sorted(Q), L] for P, Q, L in self.restrictions]}

    def resolved_restrictions(self, certify=None, workdir=None):
        out = []
        for P, Q, L in self.restrictions:
            if L == 'auto':
                L = self._auto_bound(P, Q, certify, workdir)
            out.append((set(P), set(Q), int(L)))
        self.restrictions = out
        return out

    def _auto_bound(self, P, Q, certify, workdir):
        sub = self.target.restrict(P, Q)
        if self.target.row_mode == 'monotone':
            sub.monotone_rows()
        sp = Problem(sub, self.basis, 'nf', SB(), backend=self.backend)
        sd = None
        if workdir:
            sd = os.path.join(workdir, 'restr_P%s_Q%s' % ('-'.join(map(str, sorted(P))) or 'none',
                                                        '-'.join(map(str, sorted(Q))) or 'none'))
        res = minimum(sp, smax=64, certify=certify, workdir=sd, quiet=True)
        # The bound counts gates of the restricted circuit that survive elimination; an output
        # that becomes the constant true is an eliminated gate there, not an AND [] gate, so the
        # one gate `minimum` charges for constant-true outputs is not part of the bound.
        L = res['min_size'] - sp.plan()[2]
        self.sub_results.append({'P': sorted(P), 'Q': sorted(Q), 'min_size': res['min_size'],
                                 'bound_L': L,
                                 'certified_lower_bound': res.get('all_unsat_certified'),
                                 'bundle': sd})
        return L

    # ---------- output planning (NF) ----------
    def plan(self):
        n = self.target.n
        cls = [classify_output(t, n) for t in self.target.tables]
        m = len(self.prefix)
        full = (1 << (1 << n)) - 1
        ptabs = []
        if self.prefix:
            ptabs = [0] * m
            for t in range(1 << n):
                w = lean_wires(self.prefix, [bool((t >> i) & 1) for i in range(n)])
                for j in range(m):
                    if w[n + j]:
                        ptabs[j] |= 1 << t
        true_wire = next((n + j for j in range(m) if ptabs[j] == full), None)
        extra = 1 if any(c[0] == 'true' for c in cls) and true_wire is None else 0
        outs = []
        for c, t in zip(cls, self.target.tables):
            if c[0] == 'gate' and t not in outs:
                outs.append(t)
        depend = sorted(set(i for t in outs for i in range(n) if depends_on(t, n, i)))
        return cls, outs, extra, true_wire, depend

    def encode(self, s):
        """Instance for 'exactly s gates' (None when the answer is decided without SAT,
        with the reason in the second component)."""
        tgt = self.target
        restr = self.resolved_restrictions()
        if self.mode == 'raw':
            inst = encode_raw(tgt.n, tgt.rows, tgt.tables, self.basis, s, self.exists, restr,
                              self.forbid)
            return inst, None
        cls, outs, extra, true_wire, depend = self.plan()
        snf = s - extra
        m = len(self.prefix)
        if snf < m:
            return None, 'UNSAT: fewer than the %d fixed gates (+%d constant gate)' % (m, extra)
        if not outs:
            if snf == m and not self.exists and not restr and not self.forbid:
                return None, 'SAT: every output is a constant, an input or a fixed gate'
            if snf > m and not self.exists and not restr and not self.forbid:
                return None, 'UNSAT: no gate beyond the fixed ones can be used (NF)'
        if snf == 0 and outs:
            return None, 'UNSAT: no gate for a non-trivial output'
        inst = encode_nf(tgt.n, tgt.rows, outs, self.basis, snf, self.prefix, self.sb,
                         self.exists, restr, depend, self.forbid)
        return inst, None

    def assemble(self, inst, model, s):
        """Decode a model into a full circuit for all outputs."""
        tgt = self.target
        n = tgt.n
        if inst is None:
            gates, wires = [tuple(g) for g in self.prefix], []
        else:
            gates, wires = decode(inst, model)
        if self.mode == 'raw':
            return Circuit(n, gates, wires)
        cls, outs, extra, true_wire, depend = self.plan()
        if extra:
            gates = list(gates) + [('and', [])]
            true_wire = n + len(gates) - 1
        missing = n + len(gates)
        outputs = []
        for c, t in zip(cls, tgt.tables):
            if c[0] == 'false':
                outputs.append(missing)
            elif c[0] == 'true':
                outputs.append(true_wire)
            elif c[0] == 'proj':
                outputs.append(c[1])
            else:
                outputs.append(wires[outs.index(t)])
        return Circuit(n, gates, outputs)

    def verify(self, c, s=None):
        """Exact re-evaluation with the Lean semantics on all 2^n inputs plus every side
        condition. Returns a dict of checks."""
        tgt = self.target
        n = tgt.n
        checks = {}
        checks['outputs_correct_on_all_%d_inputs' % (1 << n)] = circuit_tables(c) == tgt.tables
        checks['basis_%s_fanin2' % self.basis.name()] = self.basis.check(c)
        if s is not None:
            checks['size_le_%d' % s] = c.size <= s
        if self.prefix:
            checks['prefix'] = [tuple(g) for g in c.gates[:len(self.prefix)]] == \
                [tuple(g) for g in self.prefix]
        for (op, t) in self.exists:
            w = lean_wires(c.gates, [bool((t >> i) & 1) for i in range(n)])
            checks['exists_%s_true_on_row_%d' % (op, t)] = any(
                g[0] == op and w[n + j] for j, g in enumerate(c.gates))
        for (op, t) in self.forbid:
            w = lean_wires(c.gates, [bool((t >> i) & 1) for i in range(n)])
            checks['no_%s_true_on_row_%d' % (op, t)] = not any(
                g[0] == op and w[n + j] for j, g in enumerate(c.gates))
        for (P, Q, L) in self.restrictions:
            if L == 'auto':
                continue
            e = sum(1 for j in range(c.size) if prefix_eliminable(n, c.gates, j, P, Q))
            checks['restriction_P%s_Q%s_elim_le_%d' % (sorted(P), sorted(Q), c.size - L)] = \
                e <= c.size - L
        checks['all_ok'] = all(checks.values())
        return checks


def _now():
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())


def run_size(prob, s, certify=False, workdir=None, solver='kissat', timeout=None):
    """Decide 'some circuit of the problem's class with exactly s gates' (RAW: <= s)."""
    t0 = time.time()
    inst, reason = prob.encode(s)
    rec = {'size': s}
    if inst is None:
        rec['status'] = reason.split(':')[0]
        rec['reason'] = reason
        if rec['status'] == 'SAT':
            c = prob.assemble(None, None, s)
            rec['circuit'] = c.to_json()
            rec['verification'] = prob.verify(c, s)
        return rec, (prob.assemble(None, None, s) if rec['status'] == 'SAT' else None)
    if certify:
        comments = ['circuit_synth %s' % VERSION, json.dumps(prob.spec()), 'size %d' % s]
        r = solve_external(inst.cnf, solver=solver, workdir=workdir, proof=True,
                           timeout=timeout, tag='size%02d' % s, comments=comments)
    else:
        r = solve(inst.cnf, prob.backend, timeout=timeout)
    rec['status'] = r.status
    rec['vars'] = inst.cnf.nv
    rec['clauses'] = len(inst.cnf.clauses)
    rec['seconds'] = round(time.time() - t0, 3)
    for k in ('solver', 'solve_seconds', 'cnf_sha256', 'proof_sha256', 'proof_bytes', 'drat_trim',
              'drat_seconds',
              'cnf', 'proof'):
        if k in r.info:
            rec[k] = os.path.basename(r.info[k]) if k in ('cnf', 'proof') else r.info[k]
    c = None
    if r.status == 'SAT':
        c = prob.assemble(inst, r.model, s)
        rec['circuit'] = c.to_json()
        rec['verification'] = prob.verify(c, s)
        if not rec['verification']['all_ok']:
            raise AssertionError('decoded circuit failed verification: %s' % rec)
    return rec, c


def _bundle(prob, kind, recs, extra, workdir):
    out = {'tool': 'circuit_synth %s' % VERSION, 'date': _now(), 'query': kind}
    out.update(prob.describe())
    out['sizes'] = recs
    out.update(extra)
    if prob.sub_results:
        out['restriction_bounds'] = prob.sub_results
    unsat = [r for r in recs if r['status'] == 'UNSAT' and 'reason' not in r]
    if any('drat_trim' in r for r in recs):
        out['all_unsat_certified'] = all(r.get('drat_trim') == 's VERIFIED' for r in unsat)
    else:
        out['all_unsat_certified'] = None      # not a certified run
    if workdir:
        os.makedirs(workdir, exist_ok=True)
        with open(os.path.join(workdir, 'bundle.json'), 'w') as f:
            json.dump(out, f, indent=1, default=list)
    return out


def _log(quiet, msg):
    if not quiet:
        print(msg, flush=True)


def _lb(prob):
    return 0 if prob.mode == 'raw' else len(prob.prefix)


def minimum(prob, smax=30, certify=False, workdir=None, solver='kissat', timeout=None,
            quiet=False, smin=None):
    """Least s with a circuit (sizes searched upwards from smin). Every smaller size is UNSAT
    (certified when certify=True)."""
    prob.resolved_restrictions(certify, workdir)
    recs, circ = [], None
    lo = _lb(prob) if smin is None else smin
    for s in range(lo, smax + 1):
        rec, c = run_size(prob, s, certify, workdir, solver, timeout)
        recs.append(rec)
        _log(quiet, '  size %2d: %s %s' % (s, rec['status'], _brief(rec)))
        if rec['status'] == 'SAT':
            circ = c
            break
        if rec['status'] != 'UNSAT':
            break
    ms = circ.size if circ else None
    if circ and prob.mode == 'raw':
        ms = recs[-1]['size']
    out = _bundle(prob, 'minimum', recs, {'min_size': ms, 'searched_from': lo,
                                          'circuit': circ.to_json() if circ else None}, workdir)
    out['_circuit'] = circ
    return out


def find(prob, s, certify=False, workdir=None, solver='kissat', timeout=None, quiet=False):
    """A circuit with at most s gates: tries s, s-1, ... (NF is exact-size)."""
    prob.resolved_restrictions(certify, workdir)
    recs, circ = [], None
    sizes = [s] if prob.mode == 'raw' else range(s, _lb(prob) - 1, -1)
    for q in sizes:
        rec, c = run_size(prob, q, certify, workdir, solver, timeout)
        recs.append(rec)
        _log(quiet, '  size %2d: %s %s' % (q, rec['status'], _brief(rec)))
        if rec['status'] == 'SAT':
            circ = c
            break
        if rec['status'] != 'UNSAT':
            break
    out = _bundle(prob, 'find<=%d' % s, recs, {'found': circ is not None,
                                               'circuit': circ.to_json() if circ else None},
                  workdir)
    out['_circuit'] = circ
    return out


def prove_none(prob, s, certify=True, workdir=None, solver='kissat', timeout=None, quiet=False):
    """No circuit with at most s gates. NF: every size from the lower end up to s is UNSAT;
    RAW: size s is UNSAT (padding covers smaller sizes) unless 'exists' constraints are used."""
    prob.resolved_restrictions(certify, workdir)
    recs = []
    if prob.mode == 'raw' and not prob.exists:
        sizes = [s]
    else:
        sizes = range(_lb(prob), s + 1)
    ok = True
    for q in sizes:
        rec, c = run_size(prob, q, certify, workdir, solver, timeout)
        recs.append(rec)
        _log(quiet, '  size %2d: %s %s' % (q, rec['status'], _brief(rec)))
        if rec['status'] != 'UNSAT':
            ok = False
            break
    extra = {'proved_none': ok}
    if certify:
        extra['proved_none_certified'] = ok and all(
            r.get('drat_trim') == 's VERIFIED' or 'reason' in r for r in recs)
    return _bundle(prob, 'none<=%d' % s, recs, extra, workdir)


def _brief(rec):
    bits = []
    if 'vars' in rec:
        bits.append('%d vars %d clauses' % (rec['vars'], rec['clauses']))
    if 'seconds' in rec:
        bits.append('%.2fs' % rec['seconds'])
    if 'drat_trim' in rec:
        bits.append('drat-trim: %s' % rec['drat_trim'])
    if 'reason' in rec:
        bits.append(rec['reason'])
    return '(' + ', '.join(bits) + ')' if bits else ''
