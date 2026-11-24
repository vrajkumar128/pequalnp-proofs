# L-gct-185: 6-dim level space of 4 x 4 matrices (injection sum = 24)

Status: NOT PROVED; numerically looks FALSE (largest found: 5). The accepted L-gct-214
gives dim <= 6, so the statement is not refuted by the record; LS(4) <= 5 is the open
L-gct-091 target (its helpers are in lean/PEqualNP/Gct/Helpers/LS4).

Numerics (../L-gct-231: fast5.py, ambs/, runs4/, summarize.sh):
- control dim 5: generic search solves 8/40 (row 0 + column 0 type and others).
- dim 6 in support ansatzes (100 runs each): rows{0,1}+col0 best 0.84, rows{0,1}+cols{0,1}
  best 0.31, rows{0,1,2}+col0 best 0.25, row0+col0+doubly-centred block best 0.35.
  (Generic dim-6 run not reached in the time budget.)
- Extension test: the 10 generic 5-dim solutions have first-order extension space = L;
  row0+col0 has one extra first-order direction that fails at higher order.
