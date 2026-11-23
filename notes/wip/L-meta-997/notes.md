# L-meta-997: findings (not a proof)

Status: not proved (missing lemma); released.

## Works (on paper)
k = |y|. For k >= 1, gate t is the NOT gate N = NOT f, f monotone, f = 0 below weight k, f(y) = 1.
- C1 (N := true) is monotone and correct on light inputs; C0 (N := false) is monotone, correct on inputs
  containing y, and C0 <= C everywhere.
- Light bound = accepted L-meta-270; its cut argument on C1 gives each set meeting y at least
  min(k, |S|) - 1 gates with unit profile inside S of size >= 2 (families pairwise disjoint).
- Same argument on C0 with base y gives each set disjoint from y at least |S| - 1 gates with
  "y plus one point" profile inside S of size >= 2 (pairwise disjoint).

## Where the sketch breaks
A gate can lie in a light family (set meeting y) and a heavy family (set disjoint from y) without being a
refund gate: e.g. g = OR(AND(N, X), AND(f, X')) acts as X on light inputs and X' on heavy ones.
gap_check.py exhibits this in a fully correct circuit (gate 6: unit profile {u1, p1}, heavy profile
exactly S_2; the claim still holds there, LHS 5 vs RHS 13). So "doubly counted gates have exact
profiles" is false.

## Proved cases (paper)
- k <= 1 (heavy families alone); k = 2; every set disjoint from y has size <= k.
- k >= 2 with a good ordering of the sets disjoint from y: f(union_{j>i} S_j minus S_i) = 0 for all i
  (e.g. one such set): use light families {g : false at z_i in C1, true at two units of S_i} with
  z_i = union_{j>i} S_j minus S_i; size >= |S_i| - 1 by L-meta-529's merge invariant; disjoint, no refunds.

## Open
k >= 3, some set disjoint from y larger than k, f triggered by unions of such sets. Needs a global
charging of overlap gates. A counterexample, if any, needs n in the dozens (too big for decide).
Suggest splitting off the good-ordering case as its own step.

work/: gap_check.py, C0/C1 helper draft head.lean (uncompiled), copies of L-meta-270 / 1325 / 988.
