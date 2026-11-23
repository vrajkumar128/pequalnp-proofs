import sys
sys.path.insert(0,'.')
import synth, lns, window
nears = lns.parse_near(sys.argv[1], 19)
idx = int(sys.argv[2])
cost, c = nears[idx]
cc = window.clean(c)
names = {v: 'x%d' % v for v in range(10)}
T = window.tts(cc)
def expr(w):
    return names[w]
for i, (op, a, b) in enumerate(cc):
    g = 10 + i
    names[g] = 'g%d' % g
    print(f'g{g} = {op}({names[a]}, {names[b] if op != "not" else ""})')
# print minimal implicants of each gate (monotone) among small sets
import itertools
def minterms(tt):
    res = []
    for k in range(0, 5):
        for S in itertools.combinations(range(10), k):
            t = sum(1<<v for v in S)
            if (tt >> t) & 1 and not any(set(r) <= set(S) for r in res):
                res.append(S)
    return res
for i in range(len(cc)):
    print('g%d' % (10+i), minterms(T[10+i]))
