# L-gct-191: 8-dim level space of 4 x 6 matrices with zero row sums

Status: NOT PROVED; numerically looks FALSE (largest found: 7).

Known 7: the L-gct-180 pattern extended: rows 0..2 carry two cube-root-of-unity column
pairs (cols (0,1): rows (1, w, w^2) and minus; cols (2,3): rows (1, w^2, w) and minus) plus
row 3 free with zero sum (5 dims): 2 + 5 = 7, verified numerically (test180.py, error 1e-15).
- Three pairs (A,B,A) on rows 0..2 alone are level (3-dim) but adding row 3 breaks it.
- Ansatz "row 3 fixed (5) + k free in rows 0..2" (fixedF.py): k = 2 solved 20/30,
  k = 3 (dim 8) 0/60, best 0.50.
- Ansatz "the two cube-root pairs fixed + k free vectors in the whole zero-row-sum space":
  k = 5 (dim 7) solved 2/20; k = 6 (dim 8) 0/40, best 1.1.
- All 20 seven-dim solutions of that family have first-order extension space = L inside the
  20-dim zero-row-sum space (no extension).
- Generic zero-row-sum search misses even the known 7 (0/30), so generic negatives are weak.
  Support ansatzes at dim 8 (40 runs each): rows{0,1}+col0 best 6.5, row0+cols{0,1} 10.5,
  rows{0,1}+cols{0,1} 5.9, rows{0,1,2}+col0 3.5 (no control there, weak evidence).
