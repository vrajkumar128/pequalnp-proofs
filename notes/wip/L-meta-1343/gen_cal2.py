import sys; sys.path.insert(0,'..')
import shard_search as S
n=int(sys.argv[1]); s=int(sys.argv[2]); zr=[int(z) for z in sys.argv[3].split(',')] if sys.argv[3]!='none' else None
E=[(i,(i+1)%n) for i in range(n)]
S.OPTS.clear()
if zr: S.OPTS['zr']=zr
cnf,meta=S.encode_b(n,E,s,None)
S.write_dimacs(cnf,f'zr_c{n}_{s}_{sys.argv[3].replace(",","")}.cnf'); print(sys.argv[3], cnf.nv, len(cnf.clauses))
