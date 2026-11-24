import sys, itertools, time
from pysat.solvers import Solver
def mono_rows(n, f):
    tt=[f([(t>>i)&1 for i in range(n)]) for t in range(1<<n)]
    mins=[t for t in range(1<<n) if tt[t] and all(not tt[t&~(1<<i)] for i in range(n) if t>>i&1)]
    maxf=[t for t in range(1<<n) if not tt[t] and all(tt[t|(1<<i)] for i in range(n) if not t>>i&1)]
    return mins,maxf
def depth_sat(n, ones_rows, zero_rows, D, solver='cadical153', verbose=False):
    NI=(1<<D)-1; NL=1<<D
    cnt=[0]
    def nv(): cnt[0]+=1; return cnt[0]
    typ={i:nv() for i in range(1,NI+1)}
    sel={(l,i):nv() for l in range(NI+1,NI+NL+1) for i in range(n)}
    cls=[]
    for l in range(NI+1,NI+NL+1):
        cls.append([sel[l,i] for i in range(n)])
        for i in range(n):
            for j in range(i+1,n): cls.append([-sel[l,i],-sel[l,j]])
    def enc(t,val):
        v={k:nv() for k in range(1,NI+NL+1)}
        cls.append([v[1] if val else -v[1]])
        for k in range(1,NI+1):
            a,b,ty=v[2*k],v[2*k+1],typ[k]
            if val: cls.extend([[-v[k],-ty,a],[-v[k],-ty,b],[-v[k],ty,a,b]])
            else: cls.extend([[v[k],-ty,-a,-b],[v[k],ty,-a],[v[k],ty,-b]])
        ones=[i for i in range(n) if t>>i&1]
        for l in range(NI+1,NI+NL+1):
            if val: cls.append([-v[l]]+[sel[l,i] for i in ones])
            else:
                for i in ones: cls.append([v[l],-sel[l,i]])
    for t in ones_rows: enc(t,True)
    for t in zero_rows: enc(t,False)
    with Solver(name=solver,bootstrap_with=cls) as s:
        r=s.solve()
        if not r: return None
        m=set(x for x in s.get_model() if x>0)
        def show(k):
            if k>NI: return 'x%d'%[i for i in range(n) if sel[k,i] in m][0]
            return '('+show(2*k)+(' & ' if typ[k] in m else ' | ')+show(2*k+1)+')'
        return show(1)
def mindepth(n,f,maxD=8):
    mins,maxf=mono_rows(n,f)
    for D in range(0,maxD+1):
        t=time.time(); r=depth_sat(n,mins,maxf,D)
        print(' D=%d %s %.1fs'%(D, r if r else 'UNSAT', time.time()-t),flush=True)
        if r: return D
maj=lambda a,b,c:(a and b) or (a and c) or (b and c)
if __name__=='__main__':
    print('MAJ3'); mindepth(3,lambda z:maj(*z))
    print('C5'); mindepth(5,lambda m:any(m[v] and m[(v+1)%5] for v in range(5)))
    print('MAJ&MAJ'); mindepth(6,lambda z:maj(*z[:3]) and maj(*z[3:]))
    print('MAJ|MAJ'); mindepth(6,lambda z:maj(*z[:3]) or maj(*z[3:]))
    print('G=M0&(M1|M4)'); mindepth(9,lambda z:maj(*z[:3]) and (maj(*z[3:6]) or maj(*z[6:])))
