# L-gct-199: 5-dim doubly centred level space of 4 x 5 matrices

Status: NOT PROVED; numerically looks FALSE (no 5-dim space found; 4 is the max seen).

On doubly centred t (zero row and column sums) the conditions are S_2 = S_3 = S_4 = 0;
S_2 = (sum t_ij^2)/2 is nondegenerate on the 12-dim space, so degree 2 allows up to 6.

## Where the known 4-dim spaces live
All 4-dim solutions found have a zero row: they are 3 x 5 doubly centred level spaces
(rows 1..3, cube-root-of-unity patterns), dim q - 1 = 4. Searching in that 8-dim ansatz
finds them 101/300 times. A generic random-chart search over the full 12-dim space found
them 0/600 times, so generic negatives are weak here.
- Extension test: all 40 of those 4-dim solutions have first-order extension space equal to
  L itself inside the full 12-dim doubly centred space (extsol.py), so none extends to 5.
- A 5-dim space cannot have a zero row (3 rows: <= q - 1 = 4, L-gct-157) or a zero column
  (4 x 4 doubly centred: <= 3, L-gct-216), so it must use the full support.
- dim 5 searches: generic full space 1723 runs (runs4/T_4x5rc_m5.log), best 0.47;
  Fourier ansatzes (rows split along (1,i,-1,-i), (1,-1,1,-1), (1,-i,-1,i); columns along
  5th roots of unity, every 2- and 3-subset): dim 5 never, dim 4 never (best 0.13).
Scripts: ../L-gct-231/fast5.py (flags `rc`, AMB=ambient file), mkamb3.py, mkcolf.py, extsol.py.
