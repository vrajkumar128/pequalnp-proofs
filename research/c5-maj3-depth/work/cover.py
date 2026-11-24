#!/usr/bin/env python3
"""Can m G-images of listed sets cover all rows of a side?  (exact search)
usage: cover.py ENUM.json m"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
from rootsplit import group_perms, apply_mask

def main():
    E = json.load(open(sys.argv[1])); m = int(sys.argv[2])
    sp = gen.spec('c5'); G = group_perms(sp)
    rows = sp['A'] if E['side'] == 'a' else sp['B']
    N = len(rows)
    idx = {t: r for r, t in enumerate(rows)}
    imgs = set()
    for ent in E['sets']:
        for p in G:
            imgs.add(frozenset(idx[apply_mask(p, rows[r])] for r in ent['set']))
    # keep only maximal images
    imgs = sorted(imgs, key=len, reverse=True)
    masks = [sum(1 << r for r in I) for I in imgs]
    maxi = []
    for i, x in enumerate(masks):
        if not any((x | y) == y and x != y for y in masks[:i] if bin(y).count('1') > bin(x).count('1')):
            maxi.append(x)
    maxi = sorted(set(maxi), key=lambda x: -bin(x).count('1'))
    biggest = max(bin(x).count('1') for x in maxi)
    by_elem = [[x for x in maxi if x >> e & 1] for e in range(N)]
    print('images', len(imgs), 'maximal', len(maxi), 'largest', biggest, flush=True)
    full = (1 << N) - 1
    nodes = [0]
    def rec(cov, left):
        nodes[0] += 1
        if cov == full:
            return []
        if left == 0 or bin(full & ~cov).count('1') > left * biggest:
            return None
        e = next(i for i in range(N) if not cov >> i & 1)
        for x in by_elem[e]:
            r = rec(cov | x, left - 1)
            if r is not None:
                return [x] + r
        return None
    sol = rec(0, m)
    print('search nodes', nodes[0])
    if sol is None:
        print('NO COVER by %d images' % m)
    else:
        print('COVER FOUND:', [sorted(i for i in range(N) if x >> i & 1) for x in sol])

if __name__ == '__main__':
    main()
