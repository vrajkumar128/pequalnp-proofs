import sys, os, numpy as np
sys.path.insert(0,'/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231')
import fast5
p,q,m,trials,seed=map(int,sys.argv[1:6])
flags=sys.argv[6] if len(sys.argv)>6 else ''
os.chdir(os.path.dirname(os.path.abspath(__file__)))
fast5.run(p,q,m,trials,seed,rowzero='r' in flags,colzero='c' in flags,iters=800,tag='g_%dx%d_m%d_%s_s%d'%(p,q,m,flags or 'none',seed))
