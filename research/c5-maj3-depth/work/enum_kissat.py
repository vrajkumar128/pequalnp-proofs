#!/usr/bin/env python3
"""Enumeration loop with kissat (proof written on every call; the last, UNSAT, call's proof is
the completeness certificate). State in ENUM.json (side, k, D, sets)."""
import sys, os, json, time, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
K = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth/third_party/bin/kissat'
def main():
    st = sys.argv[1]; tag = sys.argv[2]
    E = json.load(open(st))
    sp = gen.spec('c5')
    it = 0
    while True:
        it += 1
        cnf = 'cert/%s_it%d.cnf' % (tag, it); prf = 'cert/%s_it%d.drat' % (tag, it)
        subprocess.run([sys.executable, 'enum_cnf.py', st, cnf], check=True)
        t0 = time.time()
        p = subprocess.run([K, '-q', cnf, prf], capture_output=True, text=True)
        dt = time.time() - t0
        status = [l for l in p.stdout.splitlines() if l.startswith('s ')]
        status = status[0][2:] if status else 'UNKNOWN'
        print('iter %d: %s %.1fs' % (it, status, dt), flush=True)
        if status != 'SATISFIABLE':
            break
        os.remove(prf)
        model = [int(x) for l in p.stdout.splitlines() if l.startswith('v ') for x in l[2:].split()]
        # rebuild info to decode (same build call as enum_cnf.py)
        ar = list(range(45)); br = list(range(135))
        c, info = gen.build(sp, E['D'], ar, br, sb_swap='ts', sb_var=4, sb_prec=True, sb_refl=True,
                            free_side=E['side'], atleast_k=E['k'])
        fm = gen.decode(model, info, 15)
        if E['side'] == 'a':
            assert all(not gen.ev(fm, t) for t in sp['B'])
            S = [r for r, t in enumerate(sp['A']) if gen.ev(fm, t)]
        else:
            assert all(gen.ev(fm, t) for t in sp['A'])
            S = [r for r, t in enumerate(sp['B']) if not gen.ev(fm, t)]
        print('   new set size %d: %s' % (len(S), gen.show(fm)), flush=True)
        E['sets'].append(dict(set=S, formula=gen.show(fm)))
        json.dump(E, open(st, 'w'))
if __name__ == '__main__':
    main()
