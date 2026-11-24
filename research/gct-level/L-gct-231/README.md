# L-gct-231 (probe): 3-dim space of symmetric t with perm(J + t) = 24

Status: NOT PROVED. Numerics say the statement is very likely FALSE (twin L-gct-232 true).
No Lean file was written to the checkout.

## Reduction
For a subspace L, perm(J + t) = 24 on L iff S_k(t) = 0 on L for k = 1..4, where
perm(J + t) = sum_k (4-k)! S_k(t) and S_k = sum of all k x k subpermanents of t.
For symmetric t with S_1 = 0 (all entries sum to 0):
S_2(t) = tr(t^2)/2 - |t 1|^2 (bilinear, no conjugation). Writing t = v 1^T + 1 v^T + T'
(v . 1 = 0, T' 1 = 0) this is tr(T'^2)/2 - 12 v.v, a nondegenerate form of rank 9 on the
9-dim hyperplane H, so degree 2 alone allows isotropic subspaces up to dim 4. The cubic and
quartic conditions are what kill dimension 3.

## Numerics (scripts in this folder, venv in ./venv: numpy, scipy, sympy)
- search2.py: Levenberg-Marquardt (analytic Jacobian) over the Grassmannian chart
  W = Q [I; X] of 3-planes in H, residual = perm(J + sum c_a V_a) - 24 at 2*C(7,4) random
  sample points c; reported `normres` = max |perm - 24| over 400 samples after
  orthonormalizing the basis.
  `venv/bin/python search2.py 231 <trials> <seed>`
- Results: 1000 + 200 + 120 random starts (seeds 101, 4, 1/7): best normres 6.5e-3
  (every run converges to a local minimum with residual >= 6.5e-3; restarts/BFGS
  polishing do not move them).
- Controls with the same code: 2-dim symmetric spaces (S2) converge in ~60 evaluations to
  1e-14 in 30/30 runs; general 5-dim spaces at J (J5, known to exist) are found.
- 2-dim symmetric level spaces form a 2-dim family (Jacobian rank 12 of 14, famdim.py);
  for 30 random members the first-order extension space U(L2) = {u : <grad perm(J+t), u> = 0
  for all t in L2} equals L2 (ext.py), so they do not extend to 3 dims.
- Explicit 2-dim space t = b e0^T + e0 b^T (b0 = 0, b1+b2+b3 = 0): U(L2) has dim 4,
  but the full second/third-order conditions force u in L2 (exact sympy, exts.py).
- Symmetric-group-invariant 3-dim subspaces of H (copies of the standard rep V in 2V,
  and 1 + U2): none works (exact, inv.py). Ansatz t = x y^T + y x^T, y in a 3-space: fails (xy2.py).
  Spans of 3 of the 6 Fourier matrices f_a f_b^T + f_b f_a^T (f_k = (i^(jk))_j): none (fourier.py).
- Singular slimgb on one random chart mod 32003 (rchart1.sing, 18 unknowns, 31 equations):
  killed after 5 min at 10 GB RSS (shared machine); a Groebner check is not feasible this way.

## Why no Lean proof of the twin
A proof of non-existence needs a structural argument (the J-level-space bound LS(4) <= 5
took a long case analysis); a Groebner certificate in 18 unknowns over 84 charts is out of reach.
