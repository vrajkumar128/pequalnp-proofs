# Order-3 follow-up: k = 5 K-local cases with one deficit flag fixed

This continues L-meta-957 (`../../L-meta-957/notes.md`). Everything here is an uncertified
CEGIS computation: pysat CaDiCaL 1.9.5, with the `search957.Enc` encoder
(sha256 `df0e86d7…`). It is not DRAT-certified.

## Setting

For a set K of k lines of PG(2,3) (lines {0,1,3,9}+w mod 13):
- the 13 − k lines outside K are private 3-gate OR trees;
- every OR of 2, 3 or 4 points of an outside line is a free library wire (88 wires for k = 5);
- 3k − 1 = 14 free gates with at most one NOT must compute the 5 lines of K.

UNSAT means that no 38-gate one-NOT list keeps the 8 lines outside K as private plain OR trees.
There are three k = 5 orbits under PGL(3,3), whose order is 5616:

| K | orbit size | Stab(K) order | flag orbits (rep: size) |
|---|---|---|---|
| (0,1,2,3,4) | 702 | 8 | (0,0):8, (0,3):4, (0,9):4, (3,3):2, (3,6):2 |
| (0,1,2,3,7) | 117 | 48 | (0,0):8, (0,1):4, (0,3):4, (1,1):4 |
| (0,1,2,3,9) | 468 | 12 | (0,0):3, (0,1):6, (0,3):3, (1,1):6, (1,10):2 |

A flag (i,u) means line K[i] and point u ∈ L_{K[i]}.

## Refinement and why it is sound

**Deficit flags.** Let C1 (resp. C0) be the circuit with the NOT gate set to true (resp.
false), and let m_w be the complement of line w. A flag (w,u) is a deficit flag when
C1_w(m_w) = 1 and C0_w(e_u) = 0.

**Family bound in the relaxation.** This re-derives the bound in notes.md for the free gates
only.
- A library wire T, with T ⊆ L_v for some v ∉ K and |T| ≥ 2, is never clean for w ∈ K: it is
  0 at m_w only if T ⊆ L_v ∩ L_w, which has size 1.
- So the families F1_w and F0_w (w ∈ K) consist of free gates only. They are pairwise
  disjoint, and the NOT gate is in none of them.
- Hence 1 + Σ_{w∈K} c_w ≤ (number of free gates) ≤ 3k − 1. Since c_w ≥ 3 − D_w, this gives
  D ≥ 2: at least two deficit flags on lines of K.
- This uses only the rows e_u and m_w, and those rows are in R.

**Fixing one flag.** Take any circuit of the relaxation that is correct on all inputs.
- Normalize it relative to R as in the L-meta-957 soundness note, and pad it. The result is
  correct on R, so it has two or more deficit flags.
- Map one of them to its Stab(K)-orbit representative by some σ ∈ Stab(K). σ permutes the
  inputs, the library and the lines of K.
- R is Stab(K)-invariant, so distinctness on R and correctness on R survive. Re-sort greedily.

So "rep is a deficit flag, and there are at least 2 flags" covers that whole flag orbit. Each
flag orbit is one case, and an orbit of K is decided only if all of its flag cases are UNSAT.

`kloc5.py` makes R invariant in two ways:
- R starts with no random rows: 0, the units, the pairs, and the line indicators with their
  complements. This set is PGL-invariant, and the code asserts this.
- Every counterexample row is added with its whole Stab(K)-orbit.

**NOT-position split.** `--notpos p` forces gate p to be the NOT gate; `none` means no NOT
gate. The 14 positions plus `none` cover every case.

**Checks.**
- K = (0,1), flag (0,0): s = 5, 7 and 8 UNSAT; s = 9 and 10 no answer within 120 s.
- s = 11 SAT. The decoded circuit verified on all 8192 inputs, and its deficit flags were
  recomputed as [(0,0), (0,3)]. So the flag encoding is realized.
- K = (0,1,2), flag (0,0): UNSAT in 6.1 s with CaDiCaL and 9.6 s with kissat (iteration-1
  CNF). The plain triangle case took 11 s.

## Results

Every run was on one core with a hard `timeout` cap (`run.log`, `logs/`, `sweep/`).

| K | case | NOT position | result | seconds |
|---|---|---|---|---|
| (0,1,2,3,7) | flag 0,3 | all | stopped by hand (rc -15) | 103 |
| (0,1,2,3,7) | flag 0,0 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,7) | flag 0,1 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,7) | flag 1,1 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,4) | flag 0,0 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,4) | flag 0,3 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,4) | flag 0,9 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,4) | flag 3,3 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,4) | flag 3,6 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,9) | flag 0,0 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,9) | flag 0,1 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,9) | flag 0,3 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,9) | flag 1,1 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,9) | flag 1,10 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,7) | flag 0,3 | all | no answer (cap 900 s) | 900 |
| (0,1,2,3,7) | flag 0,0 | no NOT | UNSAT | 148 |
| (0,1,2,3,7) | flag 0,0 | NOT at 13 | UNSAT | 21 |
| (0,1,2,3,7) | flag 0,0 | NOT at 12 | no answer (cap 300 s) | 300 |
| (0,1,2,3,7) | flag 0,0 | NOT at 11 | no answer (cap 300 s) | 300 |

Two more runs had no answer:
- K = (0,1,2,3,7), flag (0,0), NOT at position 6: stopped by hand after about 5 min
  (`logs/exp_*`);
- the same case at NOT position 10: stopped when the sweep was ended at 08:13. Positions 0–9
  were not run.

**What was decided.** No orbit of K and no flag case was decided. All 14 flag cases (every
flag orbit of all three k = 5 orbits) stayed in CEGIS iteration 1, on 118 rows, for the
whole 900 s cap. Iteration 1 had 22.8k variables and 534k clauses.

The only decided items are two sub-cases of K = (0,1,2,3,7), flag (0,0):
- no NOT gate: UNSAT, 147 s (this also follows from the theorem, since a flag needs a NOT);
- NOT at position 13: UNSAT, 19 s.

Neither one settles anything at the level of K. Fixing a flag did not bring k = 5 within
reach at 15 min per case. For comparison, plain k = 4 took 437–733 s, plain k = 5 (0,1,2,3,7)
gave no answer in 3000 s (L-meta-957), and on the k = 3 triangle the fixed flag took the time
from 11 s to 6 s.

The state of order 3 is therefore unchanged: no 38-gate one-NOT list keeps 9 or more lines
as private plain OR trees (k ≤ 4, L-meta-957). The k = 5 cases are open.

## Files

- `../scripts/kloc5.py`: one case (K, flag | none2 | plain, `--notpos`, `--kissat`).
- `../scripts/run_kloc.py`: job runner (cap, workers).
- `../scripts/sweep.sh`: NOT-position sweep.
- `run.log`: one line per job.
- `logs/`: per-job logs, the validation logs (`val_*`) and the experiment logs (`exp_*`).
- `sweep/`: the NOT-position sweep logs.
