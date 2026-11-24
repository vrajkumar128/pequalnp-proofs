import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
from rootsplit import group_perms, apply_mask
E = json.load(open(sys.argv[1])); minunion = int(sys.argv[2])
sp = gen.spec('c5'); G = group_perms(sp)
rows = sp['A']; idx = {t: r for r, t in enumerate(rows)}
imgs = set()
for ent in E['sets']:
    if len(ent['set']) < 12: continue
    for p in G:
        imgs.add(frozenset(idx[apply_mask(p, rows[r])] for r in ent['set']))
imgs = list(imgs)
reps = [frozenset(ent['set']) for ent in E['sets'] if len(ent['set']) >= 12]
comps = set()
for R in reps:
    for J in imgs:
        U = R | J
        if len(U) >= minunion:
            C = [r for r in range(45) if r not in U]
            comps.add(min(tuple(sorted(idx[apply_mask(p, rows[r])] for r in C)) for p in G))
print('complements (up to G) of unions of two 12-images with union >=', minunion, ':', len(comps))
for c in sorted(comps, key=len): print(len(c), list(c))
json.dump([list(c) for c in sorted(comps, key=len)], open(sys.argv[3], 'w'))
