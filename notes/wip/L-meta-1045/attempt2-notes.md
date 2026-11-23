# L-meta-1045, second attempt: no pair-level proof exists

Status: not proved (missing lemma). check.py in attempt2/ computes the statement's counts exactly.

- Every hypothesis (thin/fat, wide/narrow OR, des, Fz, non-star) depends only on wire values on inputs
  with at most two 1s ("pair level"). Forward-referenced gate inputs read false and are harmless.
- The reduction 2D >= 2*tau - 2 - 2*sum_f(tau(E_f) - 1) from attempt 1 holds.
- Obstruction: on the net graph (triangle 0,2,4 with pendants 1,3,5), the circuit
  (x1|x2|x4) & (x0|x3|x4) & (x0|x2|x5) (six ORs, two ANDs) agrees with the edge function on every input
  with at most two 1s, but has A = 2, B = 6, D = 0, Fz = 1, so A+B+2D+Fz = 9 and the right side is 11
  against |E| + 2*tau = 12; attempt 1's missing inequality A + B >= |E| + sum_f(2*tau(E_f) - 3) also
  fails (8 < 9). It is not a counterexample to the theorem only because it accepts the independent set
  {1,3,5}. So any proof must use that the circuit rejects independent sets of size >= 3.
- Likely route: odd cycles are the obstruction; for bipartite G a projection onto x_i, y_j, x_i*y_j terms
  may make a pair-level argument work (unchecked); non-bipartite needs a new idea.
- Failed: removing the output gate (shared subcircuits), gate elimination x_v := 0 (a wide OR can turn
  thin), per-wire potentials (only for unshared circuits), transfer of single-level optimality (needs
  bipartite).
