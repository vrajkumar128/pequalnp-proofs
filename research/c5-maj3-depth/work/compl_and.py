#!/usr/bin/env python3
"""For each listed minterm set C: is there a depth-D formula with root op fixed (cube) that
rejects all Bob rows and accepts every minterm of C?  Symmetry breaking: swap lex + the
stabilizer of C in G (prefix canonicity, layer precedence, block lex).  Writes cert/NAME_i.cnf
and solves it with kissat, writing a DRAT proof.
usage: compl_and.py LIST.json NAME CUBE [i ...]"""
import sys, os, json, subprocess, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
from rootsplit import group_perms, apply_mask
K = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth/third_party/bin/kissat'
L = json.load(open(sys.argv[1])); name = sys.argv[2]; cube = sys.argv[3]
which = [int(x) for x in sys.argv[4:]] or list(range(len(L)))
sp = gen.spec('c5'); G = group_perms(sp)
rows = sp['A']; idx = {t: r for r, t in enumerate(rows)}
for i in which:
    C = L[i]; Cf = frozenset(C)
    H = [p for p in G if frozenset(idx[apply_mask(p, rows[r])] for r in C) == Cf]
    c, info = gen.build(sp, 5, C, list(range(135)), sb_swap='ts', sb_var=0, subgroup=H,
                        cube={j + 1: int(ch) for j, ch in enumerate(cube) if ch in '01'})
    cnf = 'cert/%s_%d.cnf' % (name, i); prf = 'cert/%s_%d.drat' % (name, i)
    gen.write(c, cnf, comments=['depth 5, root cube %s, accepts all of C=%s, rejects all 135 Bob rows; stabilizer order %d' % (cube, C, len(H))])
    t0 = time.time()
    p = subprocess.run([K, '-q', cnf, prf], capture_output=True, text=True)
    st = [l for l in p.stdout.splitlines() if l.startswith('s ')]
    st = st[0][2:] if st else 'UNKNOWN'
    print('%s_%d |C|=%d stab=%d %s %.1fs' % (name, i, len(C), len(H), st, time.time() - t0), flush=True)
    if st == 'SATISFIABLE':
        model = [int(x) for l in p.stdout.splitlines() if l.startswith('v ') for x in l[2:].split()]
        fm = gen.decode(model, info, 15)
        print('   FORMULA', gen.show(fm), flush=True)
        os.remove(prf)
