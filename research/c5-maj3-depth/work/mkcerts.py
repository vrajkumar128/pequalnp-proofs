#!/usr/bin/env python3
"""Write the certificate CNFs into cert/ (deterministic) and list them in cert/cases.json.
Each entry: name, cnf, meaning. Run certify.py on them afterwards."""
import sys, os, json, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen

def mc(name, D, side, k, k2=0, cube='', meaning=''):
    sp = gen.spec('c5')
    ar = list(range(45)); br = list(range(135))
    c, info = gen.build(sp, D, ar, br, sb_swap='ts', sb_var=4, sb_prec=True, sb_refl=True,
                        free_side=side, atleast_k=(k, k2) if side == 'ab' else k,
                        cube={i + 1: int(ch) for i, ch in enumerate(cube) if ch in '01'})
    path = 'cert/%s.cnf' % name
    gen.write(c, path, comments=[meaning])
    return dict(name=name, cnf=path, meaning=meaning, D=D, side=side, k=k, k2=k2, cube=cube,
                vars=c.nv, clauses=len(c.cls))

if __name__ == '__main__':
    os.makedirs('cert', exist_ok=True)
    which = sys.argv[1:]
    cases = []
    spec = {
        'F1_a4_ge13': (4, 'a', 13, 0, '', 'depth 4, rejects all 135 Bob rows, accepts >= 13 minterms'),
        'R1_and5_a_ge21': (5, 'a', 21, 0, '1', 'depth 5 with root AND, rejects all Bob rows, accepts >= 21 minterms'),
        'F4_b4_ge34': (4, 'b', 34, 0, '', 'depth 4, accepts all 45 minterms, rejects >= 34 Bob rows'),
    }
    for nm in which:
        if nm.startswith('custom:'):
            _, nm2, D, side, k, k2, cube = nm.split(':')
            cases.append(mc(nm2, int(D), side, int(k), int(k2), cube, 'depth %s side %s k %s k2 %s cube %s' % (D, side, k, k2, cube)))
        else:
            D, side, k, k2, cube, meaning = spec[nm]
            cases.append(mc(nm, D, side, k, k2, cube, meaning))
    old = json.load(open('cert/cases.json')) if os.path.exists('cert/cases.json') else []
    names = {c['name'] for c in cases}
    json.dump([c for c in old if c['name'] not in names] + cases, open('cert/cases.json', 'w'), indent=1)
    for c in cases:
        print(c['name'], c['vars'], c['clauses'])
