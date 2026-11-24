import re
p='shard_search.py'
s=open(p).read()
src=open('patch_zr_code.txt').read()
s = s.replace("def encode(n, edges, s,", src + "def encode(n, edges, s,", 1)
old = "    meta = dict(n=n, s=s, op=op, A=A, B=B, rows=rows, drow=drow, enc='B')"
assert s.count(old) == 1
new = ("    if OPTS.get('zr'):\n"
       "        add_zero_restrictions(cnf, n, s, op, A, B, [(S_, b_) for (S_, b_, L_) in\n"
       "                              zero_restrictions_for(n, edges, s, OPTS['zr'])])\n" + old)
s = s.replace(old, new)
open(p,'w').write(s)
print('patched')
