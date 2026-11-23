# L-meta-519 (shard 2: two adjacent degree-3 vertices): findings (not a proof)

Status: not proved, no counterexample found (missing lemma).

## On paper
- With checked steps, a least counterexample is a "hard core" graph: it has a cycle, no good leaf, no
  thread with 4 inner degree-2 vertices, and no cheap leaf (a leaf l with tau(G-l) = tau(G) can be set to
  0, removing 1 gate, which is all it needs). So every leaf hangs on a degree-3 cycle vertex, threads have
  at most 3 inner vertices, and on a cycle a leaf is expensive exactly when both threads at its hub have
  an even number of inner vertices.
- Smallest hard cores: G4 = C7 plus leaves at 0, 3, 6 (n = 10, |E| = 10, tau = 5, bound 14; adjacent
  hubs 0~6, a shard-2 case); Theta(3,4,4) (n = 10, bound 15, shard 3); C7 with a leaf at every vertex
  (n = 14, bound 20).
- At adjacent hubs u~v, setting x_u = 1 must remove >= 5 gates but existing lemmas give <= 4, so only
  x_u = 0 (needing 3 + [tau drops] <= 4) can pay.
- Constant propagation in an ARBITRARY least circuit fails: on the tree u = x0 ~ v = x1, x2, x3 at u,
  x4, x5 at v, x6 on x2, the 8-gate least circuit
  (x4 | x5 | x0 | x2 x6) & (x1 | (x2 | x3)(x0 | x2 x6)) loses only 1 gate under x0 = 0 or x1 = 0, while
  the degree-2 vertex x2 removes 3.

## SAT experiments (exact synthesis with gate-elimination limits valid for least circuits)
Cross-checked sizes: C4 = 3, P4 = 4, P5 = 5, C5 = 7, C6 = 8, C7 = 10, C7 plus a leaf = 11.
- Candidate L2' (shard 2): in a least circuit with the largest orAncCount (the choice L-meta-522 makes),
  x_u = 0 or x_v = 0 removes >= 4 gates. Holds on 5 small trees with adjacent degree-3 vertices; fails
  without that choice (circuit above).
- Candidate L*: in every least circuit some vertex u with x_u = 0 removes >= deg(u) + 1 gates. Holds on
  P4, P5, C5, C6, C7 and four trees with adjacent degree-3 vertices; fails on C4 (as it must). L* alone
  would give the whole statement by induction on |E| (tau(G-u) >= tau(G) - 1, stars as base).
- Inconclusive (about 1 CPU-hour each, unfinished): G4 at 13 gates and Theta(3,4,4) at 14 gates found no
  circuit; L2' and L* on G4 and C7 plus a leaf did not finish.

Scripts in sat/: synth2.py (encoder), graphs.py (tau, bound, covered restrictions), oranc.py (L2'),
lstar.py and lstar_nomax.py (L*), verify_elim.py (independent check of the circuit above).
Requires python-sat.
