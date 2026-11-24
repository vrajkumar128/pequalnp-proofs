import sys, itertools, time
from fdef import MIN, MAX
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
D=int(sys.argv[1]) if len(sys.argv)>1 else 6
n=15
NI=(1<<D)-1; NL=1<<D
cnt=[0]
def nv(): cnt[0]+=1; return cnt[0]
typ={i:nv() for i in range(1,NI+1)}  # true=AND
sel={(l,i):nv() for l in range(NI+1,NI+NL+1) for i in range(n)}
rows1=[set(m) for m in MIN]
rows0=[set(range(n))-set(m) for m in MAX]  # ones of maxfalse point
cls=[]
for l in range(NI+1,NI+NL+1):
    cls.append([sel[l,i] for i in range(n)])
    for i in range(n):
        for j in range(i+1,n):
            cls.append([-sel[l,i],-sel[l,j]])
def enc(rowones, val):
    v={k:nv() for k in range(1,NI+NL+1)}
    cls.append([v[1] if val else -v[1]])
    for k in range(1,NI+1):
        a,b,t=v[2*k],v[2*k+1],typ[k]
        if val:
            cls.append([-v[k],-t,a]); cls.append([-v[k],-t,b]); cls.append([-v[k],t,a,b])
        else:
            cls.append([v[k],-t,-a,-b]); cls.append([v[k],t,-a]); cls.append([v[k],t,-b])
    for l in range(NI+1,NI+NL+1):
        if val:
            cls.append([-v[l]]+[sel[l,i] for i in rowones])
        else:
            for i in rowones: cls.append([v[l],-sel[l,i]])
for r in rows1: enc(r,True)
for r in rows0: enc(r,False)
# symmetry: root is OR (try both via arg)
if len(sys.argv)>2: cls.append([typ[1]] if sys.argv[2]=='and' else [-typ[1]])
print('vars',cnt[0],'clauses',len(cls),flush=True)
t=time.time()
with Solver(name='cadical153',bootstrap_with=cls) as s:
    r=s.solve()
    print('result',r,time.time()-t,flush=True)
    if r:
        m=set(x for x in s.get_model() if x>0)
        def show(k):
            if k>NI:
                return 'x%d'%[i for i in range(n) if sel[k,i] in m][0]
            return '('+show(2*k)+(' & ' if typ[k] in m else ' | ')+show(2*k+1)+')'
        print(show(1))
