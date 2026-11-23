import itertools
# Lean semantics: wires = inputs ++ one value per gate; missing wire reads False
def ev(op, vals):
    if op=='and': return all(vals)
    if op=='or': return any(vals)
    if op=='not': return not (vals[0] if vals else False)
def wires(gates, x):
    w=list(x)
    for op,ins in gates:
        w.append(ev(op,[w[i] if i < len(w) else False for i in ins]))
    return w
def run(dups):
    # variables: u1 u2 u3 | p1 p2 p3 | v5 v6
    u1,u2,u3,p1,p2,p3,v5,v6 = range(8); n=8
    y={u1,u2,u3}; k=3
    G=[]
    def add(op,ins): G.append((op,ins)); return n+len(G)-1
    a1=add('and',[u1,u2]); a=add('and',[a1,u3])
    t=len(G); ws=add('not',[a])
    X=add('or',[u1,p1]); Y=add('or',[v5,v6]); wY=add('or',[ws,Y]); g=add('and',[X,wY])
    for _ in range(dups): add('and',[X,wY])
    c1=add('or',[g,p2]); c2=add('or',[c1,p3]); oS=add('or',[c2,u1])
    S=[{u1,p1,p2,p3},{v5,v6}]; o=[oS,Y]; m=2; L=len(G)
    X_=lambda s: tuple(i in s for i in range(n))
    allx=[tuple(b) for b in itertools.product([False,True],repeat=n)]
    W={x:wires(G,x) for x in allx}
    # hypotheses
    assert all(len(S[i]&S[j])<=1 for i in range(m) for j in range(m) if i!=j)
    assert all((op!='not') or (n+j==n+t) for j,(op,ins) in enumerate(G))
    for i in range(m):
        for x in allx: assert W[x][o[i]]==any(x[p] for p in S[i]), (i,x)
    for x in allx:
        if sum(x)<k: assert W[x][n+t]
    assert not W[X_(y)][n+t]
    lhs=sum(len(s) if not (s&y) else min(k,len(s)) for s in S)
    unit=lambda w: {p for p in range(n) if W[X_({p})][w]}
    heavy=lambda w: {p for p in range(n) if p not in y and W[X_(y|{p})][w]}
    R=[j for j in range(L) if any(unit(n+j)==s for s in S) and any((not (s&y)) and heavy(n+j)==s for s in S)]
    # C0: NOT gate replaced by constant false
    G0=[('or',[]) if op=='not' else (op,ins) for op,ins in G]
    W0={x:wires(G0,x) for x in allx}
    A={}; B={}
    for i,s in enumerate(S):
        if s&y: A[i]=[j for j in range(L) if unit(n+j)<=s and len(unit(n+j))>=2]
        else:
            sound=lambda w: all((not W0[x][w]) or any(x[p] for p in s) for x in allx)
            supp=lambda w: {p for p in range(n) if W0[X_(y|{p})][w]}
            B[i]=[j for j in range(L) if sound(n+j) and len(supp(n+j))>=2]
    ov=set(sum(A.values(),[]))&set(sum(B.values(),[]))
    tot=sum(map(len,A.values()))+sum(map(len,B.values()))
    print(f'dups={dups} L={L} R={len(R)} m={m} LHS={lhs} RHS={L+len(R)+m} claim_ok={lhs<=L+len(R)+m}')
    print(f'  light family sizes {[len(v) for v in A.values()]}, heavy {[len(v) for v in B.values()]}, overlap gates {sorted(ov)}, refund gates {R}')
    print(f'  sum of family sizes {tot} vs L+R {L+len(R)}: {"EXCEEDS" if tot>L+len(R) else "ok"}')
for d in (0,4): run(d)
