# Certificate: C5 o MAJ3 has no monotone fan-in-2 AND/OR formula of depth <= 6

f(z) = OR_{i mod 5} (m_i AND m_{i+1}),  m_i = MAJ(z_i, z_{i+5}, z_{i+10}).
Claim: no fan-in-2 AND/OR formula with variable leaves (no constants) and depth <= 6 computes f.
Equivalently the L-meta-1404 statement (not in T 6 for the least such family T) is true and the
L-meta-1405 statement is false. (Status of each piece: see the table at the end.)

## 0. Facts used

1. Rows. A = the 45 minterms, B = the 135 maximal false points (work/rows.py; both lists are
   checked against all 2^15 inputs). A monotone formula computes f iff it is 1 on A and 0 on B.
2. Padding. A formula of depth <= d computes the same function as one on the complete binary
   tree of depth exactly d (replace a leaf x of depth < d by x AND x).
3. Symmetry. G = D5 (on the blocks {i, i+5, i+10}) x S3^5 (inside the blocks), |G| = 77760,
   preserves f, A and B.

Notation: for a formula phi, S(phi) = {a in A : phi(a) = 1}, Z(phi) = {b in B : phi(b) = 0}.

## 1. Facts certified by SAT + DRAT (all CNFs in work/cert/, built by work/gen.py)

- E4 (cert/E4a_k10.cnf): every depth-4 formula phi with Z(phi) = B and |S(phi)| >= 10 has
  S(phi) contained in one of 75 sets: the G-images of
  S1 = S(m2 AND (alpha3 OR alpha1)) (45 images) and S2 = S(m0 AND (beta1 OR m4)) (30 images),
  where alpha_i = z_i AND (z_{i+5} OR z_{i+10}), beta_i = z_{i+5} AND z_{i+10}. |S1| = |S2| = 12.
  CNF: depth-4 tree, all Bob rows rejected, a sequential counter "at least 10 minterms
  accepted", and for each of the 75 sets I the clause "some minterm outside I is accepted".
  In particular every depth-4 phi with Z(phi) = B has |S(phi)| <= 12.
- R1 (cert/R1_and5_a23.cnf): no depth-5 formula with root AND rejects all of B and accepts
  >= 23 minterms. (The depth-4 shortcut "no depth-4 formula accepts >= 23 minterms and rejects
  >= 68 Bob rows" is false: (alpha0 AND (z1 OR z6 z11)) OR m3 accepts 24 and rejects 72.)
- BOR (cert/BOR_or5_b68.cnf): no depth-5 formula with root OR accepts all 45 minterms and
  rejects >= 68 Bob rows.
- F4 (cert/F4_b34.cnf): no depth-4 formula accepts all 45 minterms and rejects >= 34 Bob rows.
- K_0..K_9 (cert/ORAND_i.cnf): for each of the 10 sets C_i (21 or 22 minterms) listed in
  work/pair_comps_2122.json, no depth-5 formula whose root is AND accepts all of C_i and
  rejects all of B.

Plus two exhaustive combinatorial checks (work/cover.py, work/triples.py, work/pairs.py):
- X1: no 4 of the 75 sets cover A; no 3 of them are pairwise disjoint.
- X2: for every pair (I1, I2) of the 75 sets with |I1 u I2| >= 23, A \ (I1 u I2) is a G-image
  of one of the C_i (the list of complements, up to G, of all pairs with union >= 21).

## 2. The argument

Let Phi have depth <= 6 and compute f; pad it: Phi = g OP h, g = g1 op g2, h = h1 op' h2 with
complete depth-4 trees g1, g2, h1, h2.

Root OR. g and h reject every Bob row (Phi does), and S(g) u S(h) = A. For an OR-rooted
child both grandchildren reject every Bob row.
- An AND-rooted child g: |S(g)| <= 22 by R1.
- An OR-rooted child g = g1 OR g2: S(g) = S(g1) u S(g2) with |S(g_i)| <= 12 (E4).
- (AND, AND): |S(g)| + |S(h)| <= 44 < 45. Impossible.
- (OR, OR): A = S(g1) u S(g2) u S(h1) u S(h2), sizes <= 12, sum >= 45. If all four have
  size >= 10, each lies in one of the 75 sets (E4) and 4 of them cover A: contradicts X1.
  Otherwise one has size <= 9, so the other three have size exactly 12, are pairwise disjoint,
  and (E4) are three of the 75 sets: contradicts X1.
- (OR, AND) (or symmetric): |S(h)| <= 22, so |S(g1)| + |S(g2)| >= 23, both >= 11, so S(g_i)
  lies in one of the 75 sets I_i (E4), |I1 u I2| >= 23, and h accepts A \ (I1 u I2), a G-image
  of some C_i (X2). Renaming the variables of h by the inverse group element gives an
  AND-rooted depth-5 formula accepting C_i and rejecting B: contradicts K_i.

Root AND. g, h accept every minterm; Z(g) u Z(h) = B.
- An OR-rooted child g: |Z(g)| <= 67 by BOR.
- An AND-rooted child g = g1 AND g2: g_i accept all of A, Z(g) = Z(g1) u Z(g2), and by F4
  |Z(g_i)| <= 33.
- (OR, OR): 67 + 67 < 135. (AND, OR): 33 + 33 + 67 < 135. (AND, AND): 4 x 33 < 135.

## 3. CNF encoding and its soundness (work/gen.py)

Complete binary tree of depth D: internal nodes 1..2^D-1 (children 2k, 2k+1) with an op bit
t_k (1 = AND); leaves 2^D..2^{D+1}-1 with one-hot selectors s_{l,v} (exactly one v of 15).
One-sided (Karchmer-Wigderson) row variables: for a minterm row r, a_{k,r} means "node k is 1
on r": a_{k,r} and t_k imply a_{2k,r} and a_{2k+1,r}; a_{k,r} and not t_k imply
a_{2k,r} or a_{2k+1,r}; at a leaf, a_{l,r} excludes every selector of a variable that is 0 in
r. Bob rows dually (b_{k,r}: "node k is 0 on r"). A required row has its root literal as a
unit clause; for "at least k rows" the root literals are free and a sequential counter asserts
that at least k of them are true (counter variables only imply counts, so any model has at
least k true root literals, and a formula with k accepted rows extends to a model by the
true counts). Soundness: in any model, by induction from the root, a_{k,r} true implies that
the formula decoded from (t, s) is 1 on r at node k (and b dually); completeness: the true
values of a formula satisfy every clause.

Symmetry breaking (all clauses mention only t, s and auxiliary variables defined from them):
fix the global order t_1..t_{2^D-1} (heap order), then s in leaf order and variable order.
Every constraint is a (possibly truncated) instance of "x >=_lex pi(x)" for a single
permutation pi of positions coming from a symmetry of the problem, with this one order, so the
lexicographically largest member of each orbit of solutions satisfies all of them:
- child swap at every internal node (the subtrees' op blocks level by level, then their leaf
  selector blocks);
- for the variable group: the first four leaves' variables form the lex-least sequence in
  their orbit (canonical prefixes enumerated exactly; gen.canon_min); value precedence of the
  three layers inside each block over the whole leaf sequence (from the layer transpositions);
  a full s-block lex constraint for each of the 9 pure block permutations.
- For K_i the instance is only invariant under Stab(C_i) in G: the same three kinds of
  constraints are used for that subgroup only (prefix canonicity by brute force over the
  subgroup, precedence for the layer transpositions in it, lex for its pure block perms).
Cube clauses (root op for K_i) are fixed op bits; every symmetry used preserves t_1.

## 4. Status table (updated at the end of the session)

| piece | CNF | kissat | drat-trim |
|---|---|---|---|
| E4 | cert/E4a_k10.cnf | UNSAT 204 s | s VERIFIED 218 s |
| K_0..K_9 | cert/ORAND_i.cnf | all UNSAT (113-338 s) | all 10 s VERIFIED (90-264 s each; cert/ORAND_i.json) |
| X1, X2 | (combinatorial) | cover.py / triples.py / pairs.py | exhaustive, no SAT solver |
| R1 | cert/R1_and5_a23.cnf | no answer after ~85 min (proof file > 7 GB), stopped | |
| BOR | cert/BOR_or5_b68.cnf | stopped after 32 min, no answer | |
| F4 | cert/F4_b34.cnf | not run to the end (an earlier 9-min run without proof gave no answer) | |

Root OR is settled once R1 is UNSAT; root AND needs BOR and F4. Until then the claim is not
certified.
