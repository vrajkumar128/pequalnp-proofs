import itertools
def maj(a,b,c): return (a and b) or (a and c) or (b and c)
def F(z):
    m=[maj(z[v],z[v+5],z[v+10]) for v in range(5)]
    return any(m[v] and m[(v+1)%5] for v in range(5))
pairs=lambda v:[(v,v+5),(v,v+10),(v+5,v+10)]
def minterms():
    res=set()
    for v in range(5):
        w=(v+1)%5
        for p in pairs(v):
            for q in pairs(w):
                res.add(frozenset(p+q))
    return sorted(res,key=sorted)
def maxterms():
    res=set()
    for j in range(5):
        cover=[c for c in range(5) if c not in (j,(j+2)%5)]
        for ps in itertools.product(*[pairs(c) for c in cover]):
            s=frozenset(x for p in ps for x in p)
            res.add(s)
    return sorted(res,key=sorted)
MIN=minterms(); MAX=maxterms()
if __name__=='__main__':
    print(len(MIN),len(MAX))
    # verify minterms/maxterms
    allin=list(range(15))
    tt=[F([(t>>i)&1 for i in range(15)]) for t in range(1<<15)]
    # minimal true points
    def mask(s): return sum(1<<i for i in s)
    mins=[t for t in range(1<<15) if tt[t] and all(not tt[t&~(1<<i)] for i in range(15) if t>>i&1)]
    maxf=[t for t in range(1<<15) if not tt[t] and all(tt[t|(1<<i)] for i in range(15) if not t>>i&1)]
    print(sorted(mins)==sorted(mask(s) for s in MIN), sorted(maxf)==sorted(((1<<15)-1)^mask(s) for s in MAX))
