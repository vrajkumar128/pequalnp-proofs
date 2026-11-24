import sys, os, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
from rootsplit import group_perms, apply_mask
E = json.load(open(sys.argv[1])); sizes = int(sys.argv[2]) if len(sys.argv) > 2 else 12
sp = gen.spec('c5'); G = group_perms(sp)
rows = sp['A']; idx = {t: r for r, t in enumerate(rows)}
imgs = set()
for ent in E['sets']:
    if len(ent['set']) < sizes: continue
    for p in G:
        imgs.add(frozenset(idx[apply_mask(p, rows[r])] for r in ent['set']))
imgs = [sum(1 << r for r in I) for I in imgs]
print('images', len(imgs))
full = (1 << 45) - 1
comps = set()
cnt = 0
for i in range(len(imgs)):
    for j in range(i + 1, len(imgs)):
        if imgs[i] & imgs[j]: continue
        for k in range(j + 1, len(imgs)):
            if (imgs[i] | imgs[j]) & imgs[k]: continue
            cnt += 1
            comps.add(full & ~(imgs[i] | imgs[j] | imgs[k]))
print('disjoint triples', cnt, 'distinct complements', len(comps))
# canonical forms of complements under G
canon = set()
for cmask in comps:
    S = [r for r in range(45) if cmask >> r & 1]
    canon.add(min(tuple(sorted(idx[apply_mask(p, rows[r])] for r in S)) for p in G))
print('complements up to symmetry', len(canon))
json.dump([list(c) for c in canon], open(sys.argv[3] if len(sys.argv) > 3 else 'triple_comps.json', 'w'))
for c in canon: print(c)
