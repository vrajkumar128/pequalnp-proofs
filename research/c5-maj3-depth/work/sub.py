#!/usr/bin/env python3
"""depth-D solvability of a sub-rectangle: Alice minterms of chosen edges vs chosen Bob rows."""
import sys, os, argparse, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen, run
def edge_of(sp, t):
    nb = sp['nb']
    m = [((t >> b) & 1) + ((t >> (b + nb)) & 1) + ((t >> (b + 2 * nb)) & 1) >= 2 for b in range(nb)]
    return [(u, v) for u, v in sp['edges'] if m[u] and m[v]]
def indep_of(sp, t):
    nb = sp['nb']
    return tuple(b for b in range(nb) if ((t >> b) & 1) + ((t >> (b + nb)) & 1) + ((t >> (b + 2 * nb)) & 1) >= 2)
if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--D', type=int, default=5)
    ap.add_argument('--edges', default='01,12,34')
    ap.add_argument('--indeps', default='all')
    ap.add_argument('--bperms', default='')  # e.g. '01234;21043'
    ap.add_argument('--sb', default='ts'); ap.add_argument('--enc', default='kw')
    ap.add_argument('--out', default='sub.cnf'); ap.add_argument('--timeout', type=float, default=None)
    a = ap.parse_args()
    sp = gen.spec('c5')
    E = [tuple(sorted((int(e[0]), int(e[1])))) for e in a.edges.split(',')]
    ar = [r for r, t in enumerate(sp['A']) if tuple(sorted(edge_of(sp, t)[0])) in E]
    if a.indeps == 'all':
        br = list(range(len(sp['B'])))
    else:
        I = [tuple(sorted((int(e[0]), int(e[1])))) for e in a.indeps.split(',')]
        br = [r for r, t in enumerate(sp['B']) if indep_of(sp, t) in I]
    sbvar = 0
    if a.bperms == 'auto':
        Es = set(E); Is = None if a.indeps == 'all' else set(I)
        st = []
        for d in sp['bperms']:
            okE = set(tuple(sorted((d[u], d[v]))) for u, v in Es) == Es
            okI = Is is None or set(tuple(sorted((d[u], d[v]))) for u, v in Is) == Is
            if okE and okI:
                st.append(d)
        sp = dict(sp); sp['bperms'] = st; sbvar = 4
        print('stabilizer block perms', st)
    elif a.bperms:
        sp = dict(sp); sp['bperms'] = [[int(ch) for ch in p] for p in a.bperms.split(';')]; sbvar = 4
    c, info = gen.build(sp, a.D, ar, br, sb_swap=a.sb, sb_var=sbvar, enc=a.enc)
    gen.write(c, a.out)
    print('rows', len(ar), len(br), 'vars', c.nv, 'clauses', len(c.cls), flush=True)
    st, model, dt = run.solve(a.out, a.timeout)
    print(st, '%.1fs' % dt, flush=True)
    if st == 'SATISFIABLE':
        fm = gen.decode(model, info, sp['n'])
        okA = all(gen.ev(fm, sp['A'][r]) for r in ar); okB = all(not gen.ev(fm, sp['B'][r]) for r in br)
        below = all(gen.ev(fm, x) <= sp['tt'][x] for x in range(1 << sp['n']))
        print('depth', gen.depth(fm), 'okA', okA, 'okB', okB, 'g<=f everywhere', below)
        print(gen.show(fm))
