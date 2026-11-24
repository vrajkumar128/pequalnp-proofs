import itertools, json, subprocess, sys, os
from concurrent.futures import ThreadPoolExecutor
TOOL = sys.argv[1]; OUT = sys.argv[2]; NMAX = int(sys.argv[3])
cache = {}
if os.path.exists(OUT):
    cache = {tuple(json.loads(k)): v for k, v in json.load(open(OUT)).items()}
def size(n, tt):
    key = (n, tt)
    if key in cache: return cache[key]
    r = subprocess.run([TOOL, "min", "--n", str(n), "--tt", hex(tt), "--basis", "full"], capture_output=True, text=True)
    s = None
    for line in r.stdout.splitlines():
        if line.startswith("min_size:"): s = int(line.split()[1])
    cache[key] = s
    return s
def save():
    json.dump({json.dumps(list(k)): v for k, v in cache.items()}, open(OUT, "w"))
def perm_tt(n, tt, p):
    r = 0
    for t in range(1 << n):
        if tt >> t & 1:
            u = 0
            for i in range(n):
                if t >> i & 1: u |= 1 << p[i]
            r |= 1 << u
    return r
for n in range(1, NMAX + 1):
    full = (1 << (1 << n)) - 1
    reps = sorted({min(perm_tt(n, tt, p) for p in itertools.permutations(range(n))) for tt in range(1, full)})
    def job(g):
        ng = full ^ g
        h = 0
        for t in range(1 << (n + 1)):
            if ((g >> (t & ((1 << n) - 1))) & 1) ^ (t >> n & 1): h |= 1 << t
        cg, cng, ch = size(n, g), size(n, ng), size(n + 1, h)
        return g, cg, cng, ch
    with ThreadPoolExecutor(2) as ex:
        for g, cg, cng, ch in ex.map(job, reps):
            m = min(cg, cng)
            flag = "" if ch == m + 4 else "  <-- DIFFERS"
            print(f"n={n} g={g:#x} C(g)={cg} C(~g)={cng} C(y^g)={ch} min+4={m+4}{flag}", flush=True)
            save()
