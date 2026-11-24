#!/usr/bin/env python3
"""Write the enumeration-completeness CNF: depth-D formula, every row of the other side
forced, at least k rows of the free side accepted (side a) / rejected (side b), plus for every
listed set S and every sigma in G the blocking clause 'some row outside sigma(S) is
accepted/rejected'. UNSAT means: every depth-D formula with >= k such rows has its row set
inside some sigma(S).
usage: enum_cnf.py ENUM.json OUT.cnf"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
from rootsplit import group_perms, apply_mask

def main():
    E = json.load(open(sys.argv[1])); out = sys.argv[2]
    side, k, D = E['side'], E['k'], E['D']
    sp = gen.spec('c5')
    G = group_perms(sp)
    rows = sp['A'] if side == 'a' else sp['B']
    idx = {t: r for r, t in enumerate(rows)}
    ar = list(range(len(sp['A']))); br = list(range(len(sp['B'])))
    c, info = gen.build(sp, D, ar, br, sb_swap='ts', sb_var=4, sb_prec=True, sb_refl=True,
                        free_side=side, atleast_k=k)
    root = info['root']
    imgs = set()
    for ent in E['sets']:
        Sset = ent['set']
        for p in G:
            imgs.add(frozenset(idx[apply_mask(p, rows[r])] for r in Sset))
    for img in sorted(imgs, key=sorted):
        c.add([root[r] for r in range(len(rows)) if r not in img])
    gen.write(c, out, comments=['enumeration completeness: side %s, depth %d, at least %d, %d listed sets, %d blocked images' % (side, D, k, len(E['sets']), len(imgs))])
    print('sets', len(E['sets']), 'images', len(imgs), 'vars', c.nv, 'clauses', len(c.cls))

if __name__ == '__main__':
    main()
