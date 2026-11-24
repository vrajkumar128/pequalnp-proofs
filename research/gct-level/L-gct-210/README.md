# L-gct-210: every 5 x 5 level space has dim <= 8 (refuted by a 9-dim space)

Status: NOT PROVED, NOT REFUTED. Numerically no 9-dim space, and not even an 8-dim one
(see L-gct-190), was found; the statement looks TRUE (and probably the truth is 7).

Level condition: sum over 5 x 5 permutations of prod (1 + t) = 120 + sum_k (5-k)! S_k(t),
so level means S_1 = ... = S_5 = 0 on L. On the 24-dim hyperplane S_1 = 0, S_2 is a
nondegenerate quadratic form (rank 24), so degree 2 alone allows dim 12.

Numerics (../L-gct-231: fast5.py, mksup.py, mkrcdc.py, ambs/, runs4/, summarize.sh).
Lesson from controls: random-chart searches over the whole space miss structured
solutions, so searches are run in support ansatzes (full rows R and full columns C free;
"dc" = plus a doubly centred block on the remaining rows and columns).
- control dim 7 (row 0 + column 0, the record): ansatz rows{0,1}+col0 solves 34/40;
  generic search 1/40.
- dim 8: rows{0,1}+col0 0/100 (best 1.63); rows{0,1}+cols{0,1} 0/80 (0.67);
  rows{0,1,2}+col0 0/80 (0.35); row0+col0+dc 0/80 (0.51); rows{0,1}+col0+dc 0/60 (0.54);
  generic 0/15 (0.37); seed "cube-root pairs on rows 0..2 + row 3" (6-dim, level) extended
  by 1 or 2 vectors: 0/20, 0/40.
- dim 9: rows{0,1}+cols{0,1} 0/60 (best 1.87); rows{0,1,2}+col0 0/60 (0.59);
  row0+col0+dc 0/26 (0.63).
- Full table: ../L-gct-231/runs4/SUMMARY.txt.
- Extension test: all 34 seven-dim solutions found have exactly one extra first-order
  direction, and adding it breaks the level property (relative error 0.6-1.3).
A proof of the bound (check mode) was not attempted: it needs the cubic and higher parts
(the L-gct-214/215-style case analysis, thousands of lines at 4 rows).
