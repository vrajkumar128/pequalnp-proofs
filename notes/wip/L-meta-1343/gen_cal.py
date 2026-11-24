import sys; sys.path.insert(0,'..')
import shard_search as S
n=int(sys.argv[1]); s=int(sys.argv[2]); enc=sys.argv[3]; tag=sys.argv[4]
S.OPTS['extra']='extra' in tag; S.OPTS['mono']='mono' in tag
E=[(i,(i+1)%n) for i in range(n)]
f=S.encode_b if enc=='b' else S.encode
cnf,meta=f(n,E,s,None,inj='inj' in tag)
S.write_dimacs(cnf,f'cal_c{n}_{s}_{enc}_{tag}.cnf'); print(tag, cnf.nv, len(cnf.clauses))
