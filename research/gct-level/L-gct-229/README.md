# L-gct-229 (probe): 6-dim level space at B = I + J (perm B = 65)

Status: NOT PROVED. Numerics say the statement is very likely FALSE (twin L-gct-230 true);
the largest level space at I + J found numerically has dimension 4.
No Lean file was written to the checkout.

## Reduction
perm(B + t) = 65 on a subspace L iff Q_k(t) = 0 on L for k = 1..4 (Q_k = degree-k part,
sum over k x k minors of t of perm(minor of t) * perm(complementary minor of B)).
Q_1(t) = sum_ij t_ij cof_ij(B) with cof_ii = 16, cof_ij = 11 (i != j).

## Known small level spaces at I + J
- one row r: t = e_r b^T with 16 b_r + 11 sum_{j != r} b_j = 0 (perm is affine in a row): dim 3.
- row 0 + column 0 together: perm is bilinear, the bilinear form is b'^T (2I + 3J) a,
  nondegenerate, so this family gives nothing beyond dim 3 (contrast J, where the form
  has rank 1 and one gets the 5-dim space of L-gct-222).
- two rows: bilinear form x^T M y with M = [[0,5,3,3],[5,0,3,3],[3,3,0,2],[3,3,2,0]] of
  rank 4: at most dim 4 from that support.

## Numerics (scripts and venv in ../L-gct-231)
`cd ../L-gct-231 && venv/bin/python search2.py <D3|D4|D5|229> <trials> <seed>`
(Levenberg-Marquardt with analytic Jacobian on the Grassmannian chart of the hyperplane
ker Q_1; normres = max |perm(B + t) - 65| over 400 random t of norm ~1 in L, basis orthonormal).
- D3: solved to 1e-14 in most runs.
- D4: solutions found (normres 5.6e-7 and 1.7e-5 in 20 runs; slow, singular convergence);
  ansatz `ansatz.py D4 1 20 1 col0` (column-0 space + one vector) also reaches 4.7e-6.
- D5: 380 runs (seeds 3, 202): best normres 6.1e-3, all runs stop at local minima;
  ansatz column-0 space + 2 vectors: best 2.8e-2 (30 runs).
- 229 (dim 6) directly: 40 runs, best normres 0.17.
- Structured (struct229.py, 30 runs each): symmetric t: dim 3 best 0.024, dim 4 best 0.56;
  t with zero row and column sums: dim 3 best 0.40, dim 5 best 0.85.
Every 6-dim level space contains 5-dim ones, so the D5 failure is the main evidence.

## Why no Lean proof of the twin
Excluding dim 6 needs a structural bound like LS(4) <= 5 at J (a long case analysis);
the quadratic condition alone only gives dim <= 7 (isotropic subspaces in 15 dims).
