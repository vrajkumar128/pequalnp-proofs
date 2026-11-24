import sys,time
from pysat.solvers import Solver
def depth_sat2(n, ones_rows, zero_rows, D, solver='cadical153'):
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
    rows=[(t,True) for t in ones_rows]+[(t,False) for t in zero_rows]
    V=[]
    for t,val in rows:
        v={k:nv() for k in range(1,NI+NL+1)}
        V.append(v)
        cls.append([v[1] if val else -v[1]])
        for k in range(1,NI+1):
            a,b,ty=v[2*k],v[2*k+1],typ[k]
            # ty -> v = a&b ; -ty -> v = a|b
            cls.extend([[-ty,-v[k],a],[-ty,-v[k],b],[-ty,v[k],-a,-b],
                        [ty,v[k],-a],[ty,v[k],-b],[ty,-v[k],a,b]])
        ones=[i for i in range(n) if t>>i&1]
        for l in range(NI+1,NI+NL+1):
            cls.append([-v[l]]+[sel[l,i] for i in ones])
            for i in ones: cls.append([v[l],-sel[l,i]])
    # lex: vec(left) >= vec(right) for each internal node
    m=len(rows)
    for k in range(1,NI+1):
        L,R=2*k,2*k+1
        eq_prev=None
        for r in range(m):
            l,rr=V[r][L],V[r][R]
            # eq_prev -> (rr -> l)
            if eq_prev is None: cls.append([-rr,l])
            else: cls.append([-eq_prev,-rr,l])
            if r<m-1:
                e=nv()
                # e -> eq_prev and (l<->rr)
                if eq_prev is not None: cls.append([-e,eq_prev])
                cls.append([-e,-l,rr]); cls.append([-e,l,-rr])
                # (eq_prev & l==rr) -> e
                base=[] if eq_prev is None else [-eq_prev]
                cls.append(base+[e,l,rr]); cls.append(base+[e,-l,-rr])
                eq_prev=e
    with Solver(name=solver,bootstrap_with=cls) as s:
        r=s.solve()
        if not r: return None
        mm=set(x for x in s.get_model() if x>0)
        def show(k):
            if k>NI: return 'x%d'%[i for i in range(n) if sel[k,i] in mm][0]
            return '('+show(2*k)+(' & ' if typ[k] in mm else ' | ')+show(2*k+1)+')'
        return show(1)
if __name__=='__main__':
    inst=open(sys.argv[1]).read().split('\n')
    n=int(inst[0]); a=list(map(int,inst[1].split()))[1:]; b=list(map(int,inst[2].split()))[1:]
    D=int(sys.argv[2])
    if len(sys.argv)>3:
        out=open(sys.argv[3]).read().split('\n')
        HA=[int(x) for l in out if l.startswith('HARD A:') for x in l.split(':')[1].split()]
        HB=[int(x) for l in out if l.startswith('HARD B:') for x in l.split(':')[1].split()]
    else: HA=range(len(a)); HB=range(len(b))
    full=(1<<n)-1
    ones=[a[i] for i in HA]; zeros=[full^b[i] for i in HB]
    print(len(ones),len(zeros),flush=True)
    t=time.time(); r=depth_sat2(n,ones,zeros,D)
    print('D=%d'%D,'SAT '+r if r else 'UNSAT','%.1fs'%(time.time()-t),flush=True)
