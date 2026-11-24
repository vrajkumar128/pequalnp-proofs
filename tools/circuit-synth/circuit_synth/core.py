"""Circuits, the exact Lean semantics, bases and targets.

Semantics copied from lean/PEqualNP/Defs/CircuitLowerBounds.lean (Circuit.wires / Circuit.eval):
  * input x has wires 0..n-1; gate j (from 0) appends wire n+j;
  * a gate reads wires by index; an index that does not exist YET (>= current number of wires,
    including the gate's own index and later gates) reads false;
  * AND l = l.all id (AND [] = true), OR l = l.any id (OR [] = false),
    NOT l = !(l.headD false) (reads only its first input; NOT [] = true);
  * the circuit's value is wire `output`, false if that wire does not exist.
A truth table is an int whose bit t is the value on the input x with x_i = bit i of t
(the convention of PEqualNP.MetaComplexity.tableIndex / tableFun).
"""
import itertools
import re

OPS = ('and', 'or', 'not')


class Circuit:
    """Gates are (op, [inputs]) with op in OPS; `outputs` is a list of wire indices (one per
    target output). A single-output Lean `Circuit` is (gates, outputs[k])."""

    def __init__(self, n, gates, outputs):
        self.n = n
        self.gates = [(op, list(ins)) for op, ins in gates]
        self.outputs = list(outputs)

    @property
    def size(self):
        return len(self.gates)

    def to_json(self):
        return {'n': self.n, 'gates': [[op, ins] for op, ins in self.gates],
                'outputs': self.outputs}

    @staticmethod
    def from_json(d):
        return Circuit(d['n'], [(g[0], g[1]) for g in d['gates']], d['outputs'])

    def __repr__(self):
        return 'Circuit(n=%d, size=%d, gates=%s, outputs=%s)' % (
            self.n, self.size, self.gates, self.outputs)

    def pretty(self):
        lines = []
        for j, (op, ins) in enumerate(self.gates):
            lines.append('  w%-3d = %s%s' % (self.n + j, op.upper(), ins))
        lines.append('  outputs: %s' % self.outputs)
        return '\n'.join(lines)


def lean_wires(gates, x):
    """Exact mirror of Circuit.wires: list of all wire values on input x (list of bools)."""
    w = list(x)
    for op, ins in gates:
        vals = [w[i] if 0 <= i < len(w) else False for i in ins]
        if op == 'and':
            r = all(vals)
        elif op == 'or':
            r = any(vals)
        elif op == 'not':
            r = not (vals[0] if vals else False)
        else:
            raise ValueError('unknown op %r' % (op,))
        w.append(r)
    return w


def lean_eval(gates, output, x):
    """Exact mirror of Circuit.eval."""
    w = lean_wires(gates, x)
    return w[output] if 0 <= output < len(w) else False


def row_input(n, t):
    return [bool((t >> i) & 1) for i in range(n)]


def circuit_tables(c):
    """Truth tables (ints) of every output of circuit c, by exact re-evaluation on all 2^n
    inputs with the Lean semantics."""
    tabs = [0] * len(c.outputs)
    for t in range(1 << c.n):
        w = lean_wires(c.gates, row_input(c.n, t))
        for k, o in enumerate(c.outputs):
            if 0 <= o < len(w) and w[o]:
                tabs[k] |= 1 << t
    return tabs


class Basis:
    """max_not = 0: monotone (AND/OR); k: at most k NOT gates; None: AND/OR/NOT unrestricted.
    Fan-in is always <= 2 (the gate lists have length <= 2)."""

    def __init__(self, max_not):
        self.max_not = max_not

    @staticmethod
    def parse(s):
        s = s.strip().lower()
        if s in ('mono', 'monotone', 'andor'):
            return Basis(0)
        if s in ('full', 'andornot', 'aon'):
            return Basis(None)
        m = re.fullmatch(r'k?not[=:]?(\d+)', s)
        if m:
            return Basis(int(m.group(1)))
        raise ValueError('basis must be mono, full or knot=K')

    @property
    def allow_not(self):
        return self.max_not is None or self.max_not > 0

    def name(self):
        if self.max_not == 0:
            return 'mono'
        if self.max_not is None:
            return 'full'
        return 'knot=%d' % self.max_not

    def check(self, c):
        """The Lean side conditions: FanInTwo (ops AND/OR/NOT, <= 2 inputs), Monotone2 when
        mono, NOT count when bounded."""
        for op, ins in c.gates:
            if op not in OPS or len(ins) > 2:
                return False
            if op == 'not' and self.max_not == 0:
                return False
        if self.max_not is not None:
            if sum(1 for op, _ in c.gates if op == 'not') > self.max_not:
                return False
        return True


def depends_on(tt, n, i):
    for t in range(1 << n):
        if not (t >> i) & 1 and ((tt >> t) & 1) != ((tt >> (t | (1 << i))) & 1):
            return True
    return False


def is_monotone(tt, n):
    for t in range(1 << n):
        if (tt >> t) & 1:
            for i in range(n):
                if not (tt >> (t | (1 << i))) & 1:
                    return False
    return True


def projection(n, i):
    return sum(1 << t for t in range(1 << n) if (t >> i) & 1)


def minterms(tt, n):
    """Minimal true points of a monotone function (as row indices)."""
    res = []
    for t in range(1 << n):
        if (tt >> t) & 1 and all(not (tt >> (t & ~(1 << i))) & 1 for i in range(n) if (t >> i) & 1):
            res.append(t)
    return res


def maxfalse(tt, n):
    """Maximal false points of a monotone function (as row indices)."""
    res = []
    for t in range(1 << n):
        if not (tt >> t) & 1 and all((tt >> (t | (1 << i))) & 1 for i in range(n) if not (t >> i) & 1):
            res.append(t)
    return res


class Target:
    """A multi-output Boolean function on n inputs.

    tables:   one truth table (int) per output, total functions on all 2^n inputs.
    rows:     the rows (input indices) the SAT encoding constrains. All 2^n rows by default.
              `monotone_rows()` replaces them by the minterms and maximal false points of the
              outputs; that is sound only for monotone circuits (see README, 'Sufficiency').
    formulas: optional Lean Bool expressions of the outputs in variables b0..b(n-1), used by the
              Lean emitter instead of `tableFun`.
    """

    def __init__(self, n, tables, names=None, formulas=None, desc=''):
        self.n = n
        self.tables = [int(t) & ((1 << (1 << n)) - 1) for t in tables]
        self.names = names or ['f%d' % k for k in range(len(tables))]
        self.formulas = formulas
        self.desc = desc
        self.rows = list(range(1 << n))
        self.row_mode = 'full'

    def monotone(self):
        return all(is_monotone(t, self.n) for t in self.tables)

    def monotone_rows(self):
        """Use the minterms and maximal false points of every output as the encoding rows."""
        assert self.monotone(), 'minterm/max-false-point rows need a monotone target'
        rs = set()
        for t in self.tables:
            rs.update(minterms(t, self.n))
            rs.update(maxfalse(t, self.n))
        self.rows = sorted(rs)
        self.row_mode = 'monotone'
        return self

    def value(self, k, t):
        return bool((self.tables[k] >> t) & 1)

    def to_json(self):
        return {'n': self.n, 'tables': [hex(t) for t in self.tables], 'names': self.names,
                'desc': self.desc, 'row_mode': self.row_mode, 'nrows': len(self.rows)}

    # ---- constructors ----
    @staticmethod
    def truth_table(n, spec, name='f'):
        """spec: hex '0x...', binary '0b...', or a string of 0/1 of length 2^n listing the
        values at rows 0, 1, 2, ... (row t: x_i = bit i of t)."""
        spec = spec.strip()
        if spec.startswith('0x'):
            tt = int(spec, 16)
        elif spec.startswith('0b'):
            tt = int(spec, 2)
        else:
            assert len(spec) == 1 << n and set(spec) <= {'0', '1'}, 'need 2^n characters 0/1'
            tt = sum(1 << t for t, ch in enumerate(spec) if ch == '1')
        return Target(n, [tt], [name], desc='truth table %s' % spec)

    @staticmethod
    def graph(n, edges, name='fG'):
        """Edge function f_G(x) = OR over edges uv of (x_u AND x_v)."""
        tt = 0
        for t in range(1 << n):
            if any((t >> u) & 1 and (t >> v) & 1 for u, v in edges):
                tt |= 1 << t
        form = ' || '.join('(b%d && b%d)' % (u, v) for u, v in edges) or 'false'
        return Target(n, [tt], [name], [form], desc='graph edge function, edges %s' % (edges,))

    @staticmethod
    def boolean_sums(n, sets):
        """Outputs y_k = OR_{i in sets[k]} x_i."""
        tabs, forms = [], []
        for S in sets:
            tabs.append(sum(1 << t for t in range(1 << n) if any((t >> i) & 1 for i in S)))
            forms.append(' || '.join('b%d' % i for i in S) or 'false')
        return Target(n, tabs, ['y%d' % k for k in range(len(sets))], forms,
                      desc='Boolean sums %s' % (sets,))

    @staticmethod
    def monotone_from_minterms(n, terms, maxfalse_given=None, name='f'):
        """Monotone f = OR over the given terms (sets of variables) of the AND of the term.
        If maxfalse_given is supplied it is checked to be exactly the set of maximal false
        points of that f (the pair (minterms, maximal false points) determines f)."""
        tt = 0
        masks = [sum(1 << i for i in T) for T in terms]
        for t in range(1 << n):
            if any((t & m) == m for m in masks):
                tt |= 1 << t
        if maxfalse_given is not None:
            mf = sorted(sum(1 << i for i in S) for S in maxfalse_given)
            assert mf == sorted(maxfalse(tt, n)), 'given maximal false points do not match'
        form = ' || '.join('(' + ' && '.join('b%d' % i for i in sorted(T)) + ')' if T else 'true'
                           for T in terms) or 'false'
        return Target(n, [tt], [name], [form], desc='monotone, minterms %s' % (terms,))

    @staticmethod
    def multi(n, tables):
        return Target(n, tables, desc='multi-output tables %s' % [hex(t) for t in tables])

    def restrict(self, P, Q):
        """f restricted by x_P = 1, x_Q = 0, as a function of the remaining variables (in
        increasing order)."""
        free = [i for i in range(self.n) if i not in P and i not in Q]
        m = len(free)
        base = sum(1 << i for i in P)
        tabs = []
        for tt in self.tables:
            r = 0
            for u in range(1 << m):
                t = base | sum(1 << free[k] for k in range(m) if (u >> k) & 1)
                if (tt >> t) & 1:
                    r |= 1 << u
            tabs.append(r)
        return Target(m, tabs, desc='restriction of [%s] by x%s=1, x%s=0' % (self.desc, sorted(P), sorted(Q)))


def classify_output(tt, n):
    """('false',), ('true',), ('proj', i) or ('gate',)."""
    full = (1 << (1 << n)) - 1
    if tt == 0:
        return ('false',)
    if tt == full:
        return ('true',)
    for i in range(n):
        if tt == projection(n, i):
            return ('proj', i)
    return ('gate',)


def all_graphs(nv):
    pairs = list(itertools.combinations(range(nv), 2))
    for m in range(1 << len(pairs)):
        yield [pairs[k] for k in range(len(pairs)) if (m >> k) & 1]
