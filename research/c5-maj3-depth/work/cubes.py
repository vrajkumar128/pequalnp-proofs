import itertools
def canonical_cubes():
    """assignments of t1..t7 (1 = AND) allowed by the swap symmetry breaking (truncated to ops)"""
    out = []
    for t in itertools.product((0, 1), repeat=7):
        t1, t2, t3, t4, t5, t6, t7 = t
        # lex (subtree 2) >= (subtree 3) on ops by level: t2 vs t3, then (t4,t5) vs (t6,t7)
        if (t2, t4, t5) < (t3, t6, t7): continue
        if t4 < t5 or t6 < t7: continue
        out.append(''.join(map(str, t)))
    return out
if __name__ == '__main__':
    c = canonical_cubes(); print(len(c)); print(' '.join(c))
