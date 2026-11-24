# L-meta-1405 / L-meta-1404: monotone depth of C5 o MAJ3 (15 inputs)

## Summary (end of session, ~13:05 UTC)
STATUS: UNDECIDED (not certified). No depth-6 formula was found; everything found points to
depth 7 (L-meta-1404 true, L-meta-1405 false). A two-level case analysis (CERTIFICATE.md)
reduces "no depth-6 formula" to a short list of SAT facts plus exhaustive combinatorial checks.
Done: E4 (kissat UNSAT, drat-trim s VERIFIED), K_0..K_9 (all 10 kissat UNSAT and drat-trim
s VERIFIED; work/cert/ORAND_i.json), X1/X2 (exhaustive). Open: R1 (needed for the root-OR
case; kissat ran ~85 min without an answer), BOR and F4 (needed for the root-AND case; BOR ran
32 min, F4 9 min, without an answer). Given R1, the root-OR case is complete; given BOR and
F4, the root-AND case is complete (CERTIFICATE.md section 2).
To resume: kissat -q work/cert/R1_and5_a23.cnf PROOF (same for BOR_or5_b68, F4_b34), then
work/check_proof.py NAME CNF PROOF.
No Lean file was written (the L-meta-1405 statement appears false; L-meta-1404 is not
expected in Lean).


f(z) = OR_i (m_i AND m_{i+1}), m_i = MAJ(z_i, z_{i+5}, z_{i+10}), i mod 5.
Question: is there a monotone fan-in-2 AND/OR formula of depth <= 6?

## Files (work/)
- rows.py: the 45 minterms and 135 maximal false points, checked by brute force over all 2^15
  inputs (both lists exact; the explicit Lean-statement formula equals f on all 2^15 inputs).
- gen.py: CNF generator (complete binary tree of depth D; op bit per internal node, one-hot
  variable selector per leaf; one-sided KW encoding or functional encoding; symmetry breaking).
- run.py: build + kissat + decode + verify on all inputs.
- cegar.py: row-CEGAR with incremental CaDiCaL (pysat, venv519).
- sub.py: depth-D solvability of a sub-rectangle (minterms of chosen edges x chosen Bob rows).

## Log
(see below; updated as runs finish)

### Calibration and side results (10:15-10:55 UTC)
- P4 o MAJ3 (12 inputs): depth 6 SAT in seconds; depth 5 UNSAT (kissat 108 s, strong SB 113 s).
- C5 o MAJ3 at depth 5, all 180 rows: UNSAT (70 s).
- Root-OR split by edges {01,12,34} vs {23,40}: the 27 minterms of edges 01,12,34 against all 135
  Bob rows are NOT depth-5 separable (UNSAT 240 s). Root-AND split by independent-set classes
  {0,2} vs {1,3,4}: the 81 Bob rows of classes 1,3,4 against all minterms NOT depth-5
  separable (UNSAT 180 s). (C_0 and C_2 = m1 or m3 or m0 m4 has depth 5.)
- The aligned sub-game (missing layer equal in both Alice blocks, Bob's single one at the same
  layer in all false blocks; 15 x 15 rows) IS depth-6 separable (SAT 28 s): no lower bound there.
- Row-CEGAR on the full depth-6 problem: random row subsets up to ~27+26 rows remain SAT.
- Depth-5 formula rejecting all 135 Bob rows and accepting 24 of the 45 minterms exists
  (so a pure counting argument at the root-OR fails):
  (((((z0&&z5)||z10)&&((z1&&z5)||(z0||z5)))&&((z4&&(z9||z14))||((z1&&z6)||(z1&&z11))))||
   (((z1&&(z6||z11))||(z3&&(z8||z13)))&&((z2&&z7)||(z2&&z12)||(z7&&z12))))
  It covers 2/3 of each of the edges 40, 01, 12, 23.

### Plan adopted at ~10:55: counting at the root + enumeration
A depth-6 formula is (after padding) g OP h with g, h of depth 5.
- OP = AND: g, h accept all 45 minterms and together reject all 135 Bob rows, so one of them
  rejects >= 68. Check: CNF "depth 5, accepts every minterm, rejects >= 68 Bob rows"
  (maxcover.py --side b --k 68). UNSAT would kill the AND case.
- OP = OR: g, h reject all Bob rows and together accept all 45 minterms, so one (say g) accepts
  >= 23. A depth-5 formula rejecting all Bob rows and accepting 24 minterms exists, so counting
  alone fails here. Refinement: enumerate (enum_large.py), up to the group G = D5 x S3^5, every
  set S of >= 23 minterms accepted by such a formula (blocking all G-images); then for each
  listed S check that A \ S is not depth-5 separable from B (compl.py, with symmetry breaking
  by the stabilizer of S). Completeness of the list = UNSAT of enum_cnf.py's CNF.

### 11:12 switch to a depth-4 decomposition (all checks are depth-4 CNFs, much faster)
Root OR, Phi = g OR h; g = g1 op g2, h = h1 op h2 with depth-4 g_i, h_i.
- op = OR: S_g = S_g1 u S_g2 with both g_i rejecting all of B: |S_gi| <= a(4).
- op = AND: S_g = S_g1 n S_g2 and Z_g1 u Z_g2 = B, so one g_i rejects >= 68 Bob rows:
  |S_g| <= c4(68) = max{|S| : depth 4, rejects >= 68 Bob rows}.
F1: a(4) <= 12 (depth 4, rejects all B, accepts >= 13 minterms: UNSAT, kissat 75 s).
- F2-type facts are NOT small: a depth-4 formula, (alpha0 alpha1) or m2, accepts 22 minterms and
  rejects 81 Bob rows; an AND-rooted depth-5 formula ((alpha0 alpha1) or m4) and (m3 or m0)
  rejects all of B and accepts 22 minterms (R1 with k=21 is SAT). So the root-OR case splits
  (OR,OR) / (OR,AND) / (AND,AND) all need covering arguments, not counting:
  (AND,AND) needs a_AND(5) >= 23; (OR,AND) needs 2 depth-4 sets + 1 AND-rooted depth-5 set to
  cover A; (OR,OR) needs 4 depth-4 sets to cover A.
- E4a (depth-4 formulas rejecting all of B; enumeration of accepted-minterm sets, cadical,
  descending k): k=12 gives exactly 2 orbits, m2 and (alpha3 or alpha1) [45 images] and
  m0 and (beta1 or m4) [30 images]; k=12 and k=11 exhausted (UNSAT 191 s, 162 s), i.e. every
  depth-4 formula below f accepting >= 11 minterms accepts a subset of one of these 75 sets.
  No 4 of the 75 sets cover A (cover.py, exhaustive, 44661 nodes).

### 11:30-11:45 two-level case analysis (see CERTIFICATE.md for the full argument)
- E4 certified: cert/E4a_k10.cnf (depth 4, rejects all B, accepts >= 10, 75 blocking clauses)
  kissat UNSAT 204 s, drat-trim s VERIFIED 218 s (cert/E4a_k10.json has SHA-256s).
- No 4 of the 75 sets cover A; no 3 of them are pairwise disjoint (exhaustive).
- Pairs of the 75 sets with union >= 21: 12 complement classes up to G (pair_comps21.json);
  those of size 21/22 (10 classes, pair_comps_2122.json) are checked: no AND-rooted depth-5
  formula rejecting B accepts all of C_i (ORAND.log, kissat with proofs in cert/ORAND_i.*).
- The depth-4 shortcut D ("no depth-4 formula accepts >= 23 and rejects >= 68") is FALSE:
  (alpha0 and (z1 or z6 z11)) or m3 accepts 24 and rejects 72. So two depth-5 facts are
  needed instead: R1' = no AND-rooted depth-5 formula rejects B and accepts >= 23 minterms
  (cert/R1_and5_a23.cnf), and BOR = no OR-rooted depth-5 formula accepts A and rejects >= 68
  Bob rows (cert/BOR_or5_b68.cnf), plus F4 (cert/F4_b34.cnf, depth 4).
- K_0..K_9 (ORAND): all 10 kissat UNSAT (113-338 s each; proofs cert/ORAND_i.drat, binary
  DRAT, 120-330 MB). Log: work/ORAND.log.
- 12:07: R1' (cert/R1_and5_a23.cnf) running since 11:42 (proof > 2.5 GB); BOR running since
  12:07; F4 queued after BOR (work/queue.sh, logs cert/NAME.kissat.out).

## Scripts added for the case analysis (work/)
- maxcover.py (cardinality CNFs: --side a|b|ab, --k, --k2, --cube), enum_large.py (pysat
  enumeration with G-orbit blocking), enum_cnf.py (completeness CNF), cover.py / triples.py /
  pairs.py (combinatorial checks), compl_and.py (K_i CNFs with stabilizer symmetry breaking),
  queue.sh (kissat with DRAT), check_proof.py / checkq.sh (drat-trim, writes cert/NAME.json).
- Symmetry-breaking sanity check: P4 o MAJ3 depth 4, max accepted minterms / rejected Bob rows
  with and without SB agree where both finished (12; k=13 UNSAT with SB, k=13 unfinished
  without SB in 60 s). SAT instances with SB still return verified formulas (P4 depth 6, etc.).
