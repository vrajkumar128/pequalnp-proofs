# L-meta-951 / L-meta-952: partial result (not a proof)

Status: not proved; released at the desk with reason `missing_lemma`.

## What is proved (Lean, compiles, no sorry): `partial_bound` in L-meta-951-partial.lean
For fan-in-at-most-two AND/OR/NOT gate lists (any number of NOT gates) computing the Boolean sums of
sets meeting pairwise in at most one point:

    sum over w of (if C1 is false on the complement of S_w at out w then |S_w| - 1 else |A0(S_w)| - 1) <= gates.length

- C0 / C1: the list with the NOT gate replaced by a constant false (`or []`) / true (`and []`);
  gate by gate C0 <= real list <= C1 (`val_le`).
- A0(S) = { u in S : C0 is true at the unit vector e_u }.
- This gives L-meta-951 outright when no set is "type-0" (C1 true on the complement of S), or when
  every type-0 set has S contained in A0(S).

## The missing lemma
Charge the deficit, the sum over type-0 sets S of |S minus A0(S)|, to gates outside the counted
families (plus the NOT gate itself, which lies in none of them). These are the points u at which only
the NOT wire makes the output fire on e_u.

## Routes that failed
1. Cut / specific-wire counting (as in L-meta-924) with a per-set choice of the C0 or C1 world: the C0
   world closes only if h(complement of U) = 1 for the union U of the cut's witness sets.
2. Restricting x_p = 1 (h(e_p) = 1) or x_m = 1 (m a minterm of h): prices every set avoiding p or m, but
   the remaining sets' gates were not shown disjoint; a two-anchor version fails on an explicit wire.
3. The L-meta-529 invariant on the real list: AND gates can cut the NOT wire's unit set down to S
   without merges the count sees.
4. Counterexample search: h = threshold-k with q < k <= q^2 shows each piece alone gives only part of
   m*q; no construction of a saving was found.
