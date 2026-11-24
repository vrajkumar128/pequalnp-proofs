# L-gct-187: 8-dim level space of 4 x 6 matrices (injection sum = 360)

Status: NOT PROVED; numerically looks FALSE (largest found: 7 = p + q - 3, the record;
also the zero-row-sum cube-root family of L-gct-191 gives 7).

Numerics (../L-gct-231: fast5.py, ambs/, runs4/):
- control dim 7 in rows{0,1}+col0: 20/30 solved.
- dim 8: rows{0,1}+col0 0/60 (best 3.5); row0+cols{0,1} 0/40 (3.6); rows{0,1}+cols{0,1}
  0/40 (1.17); row0+col0+dc 0/40 (0.72); rows{0,1,2}+col0 0/31 (0.52).
- Extension test: the 20 seven-dim solutions found have one extra first-order direction,
  and adding it breaks the level property (relative error 0.5-0.9).
