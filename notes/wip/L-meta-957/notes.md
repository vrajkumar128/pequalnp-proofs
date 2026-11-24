# L-meta-957 notes (search for a 38-gate one-NOT list for the 13 line-ORs of PG(2,3))

Program: search957.py (one file; run with tool-circuit-synth/venv/bin/python). Logs: runs/.
Older drafts (cegis957.py, plane.py, kloc.py, val*.py) are superseded by search957.py.

## Encoder
circuit_synth NF layout (A/B one-hot selectors + ladders, a <= b, a = b iff NOT, op bit, per-row
values), built incrementally in one CaDiCaL 1.9.5 (pysat) instance; CEGIS: solve on a row set R
(0, units, 78 pairs, line indicators and complements, 20 random), decode, evaluate exactly on all
8192 inputs (bit-parallel copy of Circuit.wires; checked against a Lean-style evaluator), add the
lightest wrong rows per wrong output, repeat. Symmetry breaking: greedy order (all pairs) +
distinctness on the current R (re-posted per iteration under a new activation literal); no
`used`, so the exact-s instance covers <= s (padding with fresh AND(x_i,x_j), pair rows in R).

## Family bound (redundant constraint; theorem, re-derived here, cf. L-meta-951 partial_bound)
C1/C0 = list with the NOT gate := true/false (monotone lists, C0 <= real <= C1). P1, P0 = unit
profiles. m_w = indicator of the complement of line w.
F1_w = {g : C1_g(m_w)=0, |P1(g)|>=2}, F0_w = {g : C0_g(m_w)=0, |P0(g)|>=2}.
- clean wire (value 0 at m_w) => profile inside L_w (monotone). AND of clean & anything has a clean
  child; OR of clean is clean of clean children. Hypergraph argument: every clean wire's profile
  lies in one component of the graph whose hyperedges are the clean OR gates with two non-empty
  child profiles; each component-merging gate has |P|>=2. So |F1_w| >= 3 when C1_w(m_w)=0
  (type 1: then P1(out_w)=L_w), |F0_w| >= (|A0(w)|-1)^+ with A0 = P0(out_w) (C0_w <= f_w is clean).
- disjoint: F1_w,F1_v (profile in L_w cap L_v), F0_w,F0_v likewise, F1_w,F0_v since P0 <= P1.
- the NOT gate is in none (C1 value constant 1, C0 value constant 0).
So 1 + sum_w c_w + #(other non-family gates) <= s, c_w = 3 (type 1) or (|A0|-1)^+ (type 0).
At s = 38 there are >= 2 deficit flags (w,u): w type 0, u in L_w, C0_w(e_u)=0 (then h(e_u)=0,
h(m_w)=1). PGL(3,3) (order 5616, computed) is flag-transitive: fix the flag (line 0, point 0).
Encoded with virtual rows (NOT forced to a constant) as a totalizer constraint
sum_bits + sum_g not(inF_g) <= s, plus optional per-line family sizes.

## Results
- q = 2 (Fano, 7 lines of 3): circuit_synth (validated tool), `none --sums ... --basis knot=1
  --size 13`: sizes 1..13 all UNSAT (size 13: 2034 s kissat). So no one-NOT list below 14 = 7*2:
  the q = 2 case of L-meta-952 holds (computed, not checked/certified).
- K-local cases at q = 3 (lines outside K = private 3-gate OR trees, every OR of 2/3/4 points
  of those lines offered as a free wire; 3k-1 gates with <= 1 NOT must compute the k lines of K;
  K up to PGL(3,3)). All UNSAT at the first CEGIS iteration (115-119 rows):
    k=2 (1 orbit) 0.5 s; k=3 triangle 11 s, concurrent 9 s;
    k=4 quadrilateral 733 s (kloc_234.log, same encoder before the merge; rerun in
    kloc4_orbit1_final.log), 3 concurrent + 1: 577 s, 4 concurrent: 437 s (kloc4_rest.log).
  So no 38-gate one-NOT list keeps 9 or more lines as private plain OR trees.
  k=5 orbit (0,1,2,3,7): no answer within 3000 s (runs/kloc5_o2.log); other k=5 orbits not run.
- validation (val_small.log, val_famdef2.log): XOR2/XOR3/MAJ3 one-NOT minima 4/9/4, the ten
  5-input L-meta-1444 one-NOT minima (s = min-1 UNSAT, s = min SAT), K-local with 3k gates SAT,
  family-bound constraints never cut a list (least size with a forced deficit equal with and
  without them on 4 small set systems, 8 cases). A first version had a bug for sets of size
  != 4 (bits fixed at 3); caught by this validation, fixed; q = 3 runs were unaffected.
- weakness: the full 38-gate encoding does not find even the plain 39-gate monotone list within
  100 s (minterm rows, with or without symmetry breaking), so "nothing found" by the full search
  is weak evidence; Fano's 14-gate list is found in 0.8 s.
- full 38-gate search with family bound + per-line families + flag (0,0): no answer after 38 min
  CPU in CEGIS iteration 1 (137 rows, 133k vars, 1.15M clauses); stopped (runs/full38_fam.log).
- Fano s = 13 with the family bound (my encoder): no answer in 25 min (the bound does not make
  the q = 2 instance easier; the tool's plain run took 34 min for size 13).
- small data from famdef: realizing one forced deficit costs 4-5 gates over the plain size
  (two 3-sets through a point: plain 4, least 9; triangle of 3-sets: plain 6, least 10/11;
  a 4-set and a 3-set through a point: plain 5, least 10).
