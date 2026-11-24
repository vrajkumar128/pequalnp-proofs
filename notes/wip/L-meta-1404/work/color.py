import itertools, sys
from pysat.solvers import Solver
F=open('F.inst').read().split('\n'); aF=list(map(int,F[1].split()))[1:]; bF=list(map(int,F[2].split()))[1:]
A0,B0=[list(map(int,l.split())) for l in open('F_start.txt').read().strip().split('\n')]
# B0 currently extended with block4 missing elem 0; recover the block0-3 part
mask03=sum(1<<(v+5*i) for v in range(4) for i in range(3))
Bcore=[bF[j]&mask03 for j in B0]
assert all((bF[j]&~mask03)==(1<<9)|(1<<14) for j in B0)
aidx={m:i for i,m in enumerate(aF)}; bidx={m:i for i,m in enumerate(bF)}
def perm_coords(pi,sig):
    # returns mapping coordinate c=(v+5i) -> new coordinate
    return {v+5*i: pi[v]+5*sig[v][i] for v in range(5) for i in range(3)}
def app(m,mp):
    r=0
    for c in range(15):
        if m>>c&1: r|=1<<mp[c]
    return r
D5=[]
for r in range(5):
    D5.append([(v+r)%5 for v in range(5)]); D5.append([(-v+r)%5 for v in range(5)])
S3=list(itertools.permutations(range(3)))
Aedges=set(); Bfams=[]
for pi in D5:
    for sig in itertools.product(S3,repeat=5):
        mp=perm_coords(pi,sig)
        Aset=frozenset(aidx[app(aF[j],mp)] for j in A0)
        Aedges.add(Aset)
        # B: each core b -> image core; extensions: image core + pair in block pi[4]
        blk=pi[4]
        fam=[]
        for bc in Bcore:
            ic=app(bc,mp)
            exts=[bidx[ic|(sum(1<<(blk+5*i) for i in range(3)) & ~(1<<(blk+5*k)))] for k in range(3)]
            fam.append(tuple(sorted(exts)))
        Bfams.append(tuple(sorted(fam)))
Bfams=list(set(Bfams))
print('A edges',len(Aedges),'B families',len(Bfams),flush=True)
# Alice-first: 2-color X with no monochromatic A-edge
with Solver(name='cadical153') as s:
    for e in Aedges:
        s.add_clause([j+1 for j in e]); s.add_clause([-(j+1) for j in e])
    r=s.solve(); print('Alice-first 2-colorable avoiding hard sets:',r,flush=True)
    if r: m=s.get_model(); print('X1=',[j for j in range(45) if m[j]>0])
# Bob-first: color Y (vars 1..135). family monochromatic in color c if every b has some ext colored c
with Solver(name='cadical153') as s:
    nv=[135]
    def new(): nv[0]+=1; return nv[0]
    for fam in Bfams:
        for col in (True,False):
            # require: exists b in fam with all exts != col
            ys=[]
            for exts in fam:
                y=new(); ys.append(y)
                for e in exts: s.add_clause([-y, -(e+1) if col else (e+1)])
            s.add_clause(ys)
    r=s.solve(); print('Bob-first 2-colorable avoiding hard sets:',r,flush=True)
    if r: m=s.get_model(); print('Y1=',[j for j in range(135) if m[j]>0])
