# Level-space searches for the GCT search steps (L-gct-181 to L-gct-219)

Each step folder holds the step, its statement, and a README with the result.
The scripts and the full results table are in L-gct-231/ (runs4/SUMMARY.txt).

| step | asks for | result |
|---|---|---|
| L-gct-181 | 4 x 5, dim >= 8 | refuted by the merged L-gct-215 (see refutations/) |
| L-gct-182 | 4 x 4 doubly centred, dim 4 | refuted by the merged L-gct-216 (see refutations/) |
| L-gct-185 | 4 x 4, dim 6 | not found; best residual 0.25 |
| L-gct-187 | 4 x 6, dim 8 | not found; best residual 0.52 |
| L-gct-190 | 5 x 5, dim 8 | not found; best residual 0.35 |
| L-gct-191 | 4 x 6 zero row sums, dim 8 | not found; best 0.50; a 7-dim space exists |
| L-gct-199 | 4 x 5 doubly centred, dim 5 | not found; best 0.47; every 4-dim space found has a zero row and does not extend to first order |
| L-gct-210 | 5 x 5, every space dim <= 8 | consistent: no 9-dim (best 0.59), no 8-dim |
| L-gct-219 | 4 x 5, no 7-dim space | consistent: 0 of 930 restricted runs solved; its suggested route fails (the degree-2 part on the zero-sum hyperplane is a full-rank quadratic form, which allows 9-dim isotropic subspaces) |

Caveat: an unrestricted random-start search misses structured solutions. In controls it found
the known 4-dim doubly centred 4 x 5 space 0 times in 600 runs. Most runs therefore restrict
the support to chosen rows and columns, where the known lower dimensions are found in 66 to 89
percent of runs. Every lower-dimensional solution found was also tested for a one-dimensional
extension; none extends.
