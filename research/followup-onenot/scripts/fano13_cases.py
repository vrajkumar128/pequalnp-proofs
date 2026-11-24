"""Size-13 case split for the Fano one-NOT question (certified with kissat DRAT + drat-trim).

Builds, with the validated circuit_synth encoder and exactly the CLI's settings
(`none --sums FANO --basis knot=1`, full 128 rows, NF, sb=all), the size-13 instance
"exactly 13 NF gates", writes it as base.cnf with the tool's own header comments (so its
SHA-256 equals the hash `circuit_synth recheck` regenerates), and writes one CNF per case:
the base clauses plus a few unit clauses (the case cube) appended at the end.

Cases (see CERTIFICATE.md for the covering argument):
  G = first gate (gate 0, wire 7) in {NOT x0, OR(x0,x1), AND(x0,x1)}   [Fano symmetry]
  for G = OR/AND: additionally split on the NOT position p in {none, 1..12}   [propositional]

usage: fano13_cases.py OUTDIR
"""
import hashlib
import json
import os
import sys

TOOL = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth'
sys.path.insert(0, TOOL)
from circuit_synth.core import Target, Basis          # noqa: E402
from circuit_synth.encode import SB                    # noqa: E402
from circuit_synth.synth import Problem, VERSION       # noqa: E402

FANO = [sorted({(u + w) % 7 for u in (0, 1, 3)}) for w in range(7)]
SUMS = ';'.join(','.join(map(str, L)) for L in FANO)
S = 13


def problem():
    tg = Target.boolean_sums(7, FANO)          # rows: full (default), as the CLI does for knot=1
    return Problem(tg, Basis.parse('knot=1'), 'nf', SB.parse('all'))


def main(out):
    os.makedirs(out, exist_ok=True)
    prob = problem()
    inst, reason = prob.encode(S)
    assert inst is not None, reason
    cnf, meta = inst.cnf, inst.meta
    assert meta['free'] == list(range(S)) and not meta['single_last']
    comments = ['circuit_synth %s' % VERSION, json.dumps(prob.spec()), 'size %d' % S]
    base_text = cnf.dimacs(comments)
    base_sha = hashlib.sha256(base_text.encode()).hexdigest()
    with open(os.path.join(out, 'base_size13.cnf'), 'w') as f:
        f.write(base_text)
    A, B, op, isnot = meta['A'], meta['B'], meta['op'], meta['isnot']
    n = meta['n']
    first = {
        'not_x0': ([A[0][0], B[0][0]], 'gate0 = NOT(x0)  [A0=0, B0=0; isnot0 follows]'),
        'or_x0x1': ([A[0][0], B[0][1], -op[0]], 'gate0 = OR(x0,x1)  [A0=0, B0=1, op0=OR]'),
        'and_x0x1': ([A[0][0], B[0][1], op[0]], 'gate0 = AND(x0,x1)  [A0=0, B0=1, op0=AND]'),
    }
    cases = []
    for g in ('not_x0', 'or_x0x1', 'and_x0x1'):
        lits, desc = first[g]
        if g == 'not_x0':
            subs = [('', [], '')]
        else:
            subs = [('_nonot', [-isnot[j] for j in range(S)], 'no NOT gate (all isnot_j false)')]
            subs += [('_not%02d' % j, [isnot[j]], 'NOT gate at position %d (isnot_%d)' % (j, j))
                     for j in range(1, S)]
        for suf, extra, d2 in subs:
            name = g + suf
            cube = list(lits) + list(extra)
            com = comments + ['case %s: %s%s' % (name, desc, ('; ' + d2) if d2 else ''),
                              'case cube (unit clauses appended): %s' % ' '.join(map(str, cube))]
            text = cnf.dimacs(com)
            # append the cube as unit clauses: rewrite the p line
            head, body = text.split('p cnf %d %d\n' % (cnf.nv, len(cnf.clauses)), 1)
            text = head + 'p cnf %d %d\n' % (cnf.nv, len(cnf.clauses) + len(cube)) + body + \
                ''.join('%d 0\n' % l for l in cube)
            fn = 'case_%s.cnf' % name
            with open(os.path.join(out, fn), 'w') as f:
                f.write(text)
            cases.append({'name': name, 'cnf': fn, 'cube': cube, 'first_gate': g,
                          'desc': desc + (('; ' + d2) if d2 else ''),
                          'cnf_sha256': hashlib.sha256(text.encode()).hexdigest()})
    varmap = {'A[0][0]': A[0][0], 'A[0][1]': A[0][1], 'B[0][0]': B[0][0], 'B[0][1]': B[0][1],
              'op[0] (true=AND)': op[0], 'isnot[j]': [isnot[j] for j in range(S)],
              'n_inputs': n, 'wires_of_gate0': n}
    info = {'tool': 'circuit_synth %s' % VERSION, 'cli_equivalent':
            "circuit_synth_cli none --sums '%s' --basis knot=1 --size 13" % SUMS,
            'fano_lines': FANO, 'size': S, 'spec': prob.spec(), 'vars': cnf.nv,
            'clauses': len(cnf.clauses), 'base_cnf': 'base_size13.cnf', 'base_cnf_sha256': base_sha,
            'variables': varmap, 'cases': cases}
    with open(os.path.join(out, 'cases.json'), 'w') as f:
        json.dump(info, f, indent=1)
    print('base', cnf.nv, 'vars', len(cnf.clauses), 'clauses', base_sha)
    print(len(cases), 'cases written')


if __name__ == '__main__':
    main(sys.argv[1])
