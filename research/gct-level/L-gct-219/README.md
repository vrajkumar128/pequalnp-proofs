# L-gct-219: no 7-dim level space of 4 x 5 matrices (injection sum = 120)

Status: NOT PROVED, numerically looks TRUE (no 7-dim space found). Not refuted.

## Same object as L-gct-181 / L-gct-215
sum_{f : Fin 4 -> Fin 5 injective} prod_i (1 + t(i, f i)) = 120 + 24 S_1 + 6 S_2 + 2 S_3 + S_4
(S_k = sum of all k x k subpermanents), so the condition is exactly S_1 = ... = S_4 = 0 on L,
i.e. the hypotheses of L-gct-181 and of the accepted L-gct-215 (dim <= 7). L-gct-181 (dim >= 8)
is now refuted from L-gct-215. Known: 6 (row 0 + column 0; also a second family supported on
rows {0,1} + one column, found numerically).

## The sketch in gap.json cannot work as stated
Degrees 1 and 2 alone do not bound the dimension by 6: on the hyperplane S_1 = 0 (19-dim)
S_2 is a NONDEGENERATE quadratic form (rank 19, q2rank.py), so isotropic subspaces of dim 9
exist. Any proof must use the cubic/quartic parts.

## Numerics (scripts in ../L-gct-231: fast5.py, ambs/, runs4/, summarize.sh)
Levenberg-Marquardt over Grassmannian charts, residual = injection sum - 120 at random
points of L, `normres` = max error over 400 random unit points after orthonormalising.
A caution learned on the controls: generic random-chart searches MISS structured solutions
(e.g. the known 4-dim doubly centred 4 x 5 space, 0/600), so the searches below are run in
support-restricted ansatz spaces (rows R and columns C fully free; "dc" = plus a doubly
centred block on the other rows/columns), where controls succeed 80-90% of the time.
- control dim 6 in rows{0,1}+col0: 50/60 solved (1e-14).
- dim 7: rows{0,1}+col0: 0/300 (best 1.78); row0+cols{0,1}: 0/300 (1.90);
  rows{0,1}+cols{0,1}: 0/110 (0.72); rows{0,1,2}+col0: 0/100 (0.45);
  row0+cols{0,1,2}: 0/100 (0.47); row0+col0+dc: 0/100 (0.61); rows{0,1}+col0+dc: 0/100 (0.58);
  rows{0,1,2}+cols{0,1}: 0/60 (0.39). (Generic run not reached in the time budget.)
- Full table: ../L-gct-231/runs4/SUMMARY.txt.
- First-order extension test: every 6-dim solution found (38) has exactly one extra
  first-order direction u, and span(L, u) is not level (relative error 0.5-1.0).
