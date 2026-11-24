import sys, itertools, time
sys.path.insert(0, '.')
import shard_search as S

def brute(n, edges, s, dirty):
    """Plain class: exactly s gates, each AND/OR of two distinct earlier wires, every gate
    but the last read later, output = last gate; no ordering/dedup. Returns a circuit or None."""
    N = 1 << n
    full = (1 << N) - 1
    tts = []
    for i in range(n):
        tts.append(sum(1 << m for m in range(N) if (m >> i) & 1))
    f = sum(1 << m for m in range(N) if S.edge_fn(edges, [bool((m >> i) & 1) for i in range(n)]))
    dbit = None if dirty is None else sum(1 << i for i in dirty)
    gates = []
    used = [0] * (n + s)
    def rec(j):
        if j == s:
            if tts[-1] != f: return False
            if any(used[n + k] == 0 for k in range(s - 1)): return False
            if dbit is not None and not any(gates[k][0] == 'AND' and (tts[n + k] >> dbit) & 1 for k in range(s)): return False
            return True
        unused = sum(1 for k in range(j) if used[n + k] == 0)
        r = s - j
        if unused - (r - 1) > 1 + 0 and unused > r + 1 - 1 + 1: pass
        W = n + j
        for b in range(W):
            for a in range(b):
                # liveness pruning: after this gate, unused' >= unused - (#unused among a,b) + 1, need unused' - (r-1) <= 1
                nu = unused - (1 if a >= n and used[a] == 0 else 0) - (1 if b >= n and used[b] == 0 else 0) + 1
                if nu - (r - 1) > 1: continue
                for o in ('AND', 'OR'):
                    v = (tts[a] & tts[b]) if o == 'AND' else (tts[a] | tts[b])
                    tts.append(v); gates.append((o, [a, b])); used[a] += 1; used[b] += 1
                    ok = rec(j + 1)
                    if ok: return True
                    tts.pop(); gates.pop(); used[a] -= 1; used[b] -= 1
        return False
    return list(gates) if rec(0) else None

def min_brute(n, edges, dirty, smax):
    for s in range(1, smax + 1):
        c = brute(n, edges, s, dirty)
        if c is not None:
            return s, c
    return None, None

def graphs_upto_iso(n):
    allpairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    seen = set(); out = []
    for k in range(1, len(allpairs) + 1):
        for es in itertools.combinations(allpairs, k):
            canon = min(tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in es)) for p in itertools.permutations(range(n)))
            if canon in seen: continue
            seen.add(canon); out.append(list(es))
    return out

if __name__ == '__main__':
    t0 = time.time()
    n = int(sys.argv[1]); smax = int(sys.argv[2])
    mism = 0; checked = 0
    for edges in graphs_upto_iso(n):
        for D in [None] + S.maximal_independent_sets(n, edges):
            sb, cb = min_brute(n, edges, D, smax)
            ss, cs, res = S.min_size(n, edges, D, smax=smax)
            ss2, cs2, res2 = S.min_size(n, edges, D, smax=smax, order=False)
            ss3, cs3, res3 = S.min_size(n, edges, D, smax=smax, enc='B')
            ss4, cs4, res4 = S.min_size(n, edges, D, smax=smax, enc='B', order=False)
            checked += 1
            flag = 'OK' if (sb == ss == ss2 == ss3 == ss4) else 'MISMATCH'
            if flag != 'OK': mism += 1
            print(f'n={n} E={edges} D={D}: brute={sb} sat_order={ss} sat_noorder={ss2} B={ss3} Bno={ss4} {flag}', flush=True)
    print(f'checked {checked}, mismatches {mism}, time {time.time()-t0:.1f}s')
