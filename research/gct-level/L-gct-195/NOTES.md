# L-gct-195 / L-gct-196 notes

Statement: level space L of 4 x q matrices (e_1..e_4 = sums of k x k subpermanents vanish
on L), q = 6: dim L <= 8; q = 7: dim L <= 9. Equivalent: per(J + t) = q!/(q-4)! on L.

## Skeleton of the merged L_gct_215 (4 x 5, dim <= 7)

Top level (Ac.aAm / Ac.aDe): assume dim >= 8, take an 8-dim S <= L. Let
u_i = dim of the part of S supported on row i (zero-sum row vectors), p_ij = rank of the
projection of S to rows i, j. Cases:

1. some u_i >= 4 = q - 1 (vJ, Ac.aEn -> Av.aG7). The row-i part is ALL zero-sum vectors.
   Then for every t the cofactor vector (3 x 4 subpermanent sums with column j deleted) is
   constant in j; scaling gives S1 = Q2 = G3 = 0 column by column; the other three rows
   decompose as (a+b, w a + w^2 b, w^2 a + w b) with w^2 + w + 1 = 0 (vN), and xO/vM give
   dim(L cap ker row_i) <= 3. So dim <= 4 + 3. GENERALIZES to any q: u_i = q-1 => dim <= q+2.
2. some u_i in {2,3} (MidCase, Ac.Af, ~1800 lines): W L i = span{1} + projection to the
   other 3 rows (3 x 5), half-centred entries aA, 2-dim U L i analysed by kT, sub-cases
   kV (u = 2, U = bJ A, |A| = 3), fD, lT (u = 3), cube roots again (M3.qR, aEl).
3. some u_i = 1 (mI, Ac.Ah): build a 7-dim level space with two equal columns (vI), and
   eI (Ac.Ad, ~900 lines): a 7-dim level space at 4 x 5 with two equal columns does not
   exist (bilinear form B, rank vectors r L i, p L i j <= r L i + r L j, aBv combinatorics).
4. all u_i = 0:
   HighPair (Ac.Ar etc.): some p_ij = 7 = 2q - 3; sub-cases aBo in {4,5,6}.
   vK (Ac.aGe): all p_ij <= 6; finds rows with aE = 4, symmetric matrix G with
   Z_ij Z_jk Z_ki = 0, isotropic counting yQ: dim L + k <= 9 + ... .

Basic tools: lO (row hyperplane: row_i(L) avoids 1, so lies in ker f_i with f_i 1 = 1),
cD/aBr/lB (two rows with x_c y_d + x_d y_c = 0 kill per, so p_ij <= 2q - 3), the bilinear
form B of e_2 (L is totally isotropic; isotropic bound floor((4q-1)/2) = 9 at q = 5),
permutation symmetry Perm(Fin 4) x Perm(Fin 5).

## Where q = 5 is essential

* dim L = q + 3 against the e_2 isotropy bound floor((4q-1)/2) = 2q - 1: slack 1 at q = 5
  (8 vs 9), slack 2 at q = 6, 3 at q = 7. The vK/HighPair counting (yQ) uses slack 1.
* lB: p_ij <= 2q - 3 = 7 < 8 = dim L at q = 5, so two-row projections have a kernel. At
  q = 6 the bound is 9 = dim L: no information.
* The avoidance arguments use linear subspaces Z inside {per = 0} with codim Z <= dim L
  (only then can L + Z contain J): two rows on one column (codim 2(q-1)) and four rows on
  three columns (codim 4(q-3)) both have codim 8 = q + 3 exactly at q = 5. For q >= 6 the
  only such Z of codim <= q + 3 is {a row is zero}, i.e. lO. So for q >= 6 a proof must
  use polynomial identities (per constant), not only "J + L avoids per = 0".
* Many sub-cases are explicit Fin 5 configurations (A3 = {0,1,2}, rad Z = (a,a,a,b,-a-b),
  |A| = 3, aBo in {4,5,6}). Conclusion: a mechanical 4 x 6 copy is not possible; the
  numerology changes in every case.

## Tools proved for all q in the library (PEqualNP.Gct)

* L156: 3 x q level => dim <= q + 1. L157: centred 3 x q => dim <= q - 1.
* L101: 2 x q level => dim <= q - 1.
* L175 / Helpers/ColumnCore (+ L171 Rado, RadoLinear): if J in V, lam J = 1 and
  sum_j prod_i x(i,j) = q lam(x)^p on V then dim V <= q (column-product core, induction
  on columns + Rado transversal: one zero per column).

## Reductions found here

* Row deletion: some row map of rank <= 1 => dim L <= 1 + f(3,q) <= q + 2 (L156).
* Column deletion: some column map of rank <= 1 => dim L <= 1 + f(4,q-1).
* Row-sum map rho : L -> 1^perp (rank r <= 3), L_0 = centred part. On L_0 the column
  product sum is sum_j prod_a (1 + y_aj) = q + mu_0123(y) = q + P(y)/6 with
  P = mu01 mu23 + mu02 mu13 + mu03 mu12 (mu_S = sum_j prod_{a in S} y_aj). So any
  P-null subspace W of L_0 has dim W <= q - 1 (ColumnCore). Hence: if L_0 has a P-null
  subspace of codim <= 3 - r in L_0, then dim L <= q + 2.
* Numerics (saved solutions of L-gct-231): in every r >= 2 example (rows{0,1}+col0
  families at 4x5 dim 6 and 4x6 dim 7) P vanishes on L_0; in the r = 0 examples (cube-root
  family, F_ab5) P does not vanish on L_0 = L, dim L_0 = q + 1.
* Rado + one zero per column on a centred L of dim q + k: on E_sigma (dim k + 1) P is
  -6 q kappa^4 (a 4th power of a linear form), and P vanishes on D_sigma (dim k).
  Equivalently: for centred level x, f_x(c) = sum_j prod_a (c + x_aj) = q c^4 + mu_0123(x),
  so every value v common to all columns of x has v^4 = -mu_0123(x)/q.
* More numerics (num/analyze.py, num/transv.py, num/g1test.py):
  - every saved example with r >= 1 (4x4 dim 5, 4x5 dim 6, 4x6 dim 7) has P = 0 on L_0,
    so its L_0 obeys the column-product core;
  - but this is not a general identity: num/g1test.py finds 2-dim level spaces
    span(y, s), y centred, rho(s) != 0, with P(y) = 1 (q = 4, hence any q >= 4);
  - "some transversal of coordinates plus rho has rank <= 3 on L" fails for a 4x4 dim 5
    example (f_4x4_m5_none_s3_t19, min rank 4), so W = centred zero-transversal part is
    not always of codim <= 3.
* Rado with one zero per column + IH (column deletion) gives a Hall surplus of only 1;
  killing the error term P needs about 2q zeros (two per column: then
  sum over the four row triples of the triple column products is 4q != 0 on L_0).

## Status

NOT PROVED. The gap: for q >= 6 a proof needs either (a) a P-null centred subspace of
codim <= 3 (then ColumnCore gives q + 2), or (b) a row or column of rank <= 1 (then L156
or the q-1 bound gives q + 2). Neither follows from the tools above. The r = 0 (centred)
case alone already contains the cube-root family of dim q + 1.
Nothing was written to lean/PEqualNP/Outside.
