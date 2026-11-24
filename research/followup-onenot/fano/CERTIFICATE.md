# Certificate: no one-NOT circuit with at most 13 gates for the Fano line-ORs

## Claim

Let the Fano plane have points 0..6 and lines {0,1,3}+w mod 7:
{0,1,3}, {1,2,4}, {2,3,5}, {3,4,6}, {0,4,5}, {1,5,6}, {0,2,6}. Let y_L = OR of x_i over the
points i of the line L.

**No fan-in-2 AND/OR/NOT gate list with at most one NOT gate and at most 13 gates computes all
seven y_L.** (The outputs share one gate list, as in `circuit_synth --sums`. The circuit model
is the Lean `FanInTwo` model of the pequalnp.com library.) Seven lines × two ORs gives a
monotone circuit with 14 gates, so 14 is the least size with at most one NOT gate.

Equivalent command line, as in the earlier uncertified run (2034 s for size 13):
`circuit_synth_cli none --sums '0,1,3;1,2,4;2,3,5;3,4,6;0,4,5;1,5,6;0,2,6' --basis knot=1 --size 13`.

## What is certified by DRAT, and what is not

The certified part is propositional. drat-trim checked that each of these CNF files is
unsatisfiable:
- the tool's CNFs for exactly s NF gates, s = 1..12 (`sizes01-12/`);
- 27 case CNFs for s = 13 (`size13/`). Each one is the tool's size-13 CNF plus a few unit
  clauses (the case cube).

Two further propositional checks:
- **Coverage of the NOT-position split.** For the first gate OR(x0,x1) and for AND(x0,x1), the
  14 sub-cubes (no NOT; NOT at position p = 1..12) cover every model of the base CNF plus the
  first-gate cube. NOT at position 0 is impossible there. This was checked by unit propagation
  and by drat-trim with an empty proof: `split_validation/coverage_*.cnf`, both `s VERIFIED`.
- **Hashes.** The size-13 base CNF has exactly the bytes the tool produces for size 13:
  - the same code path reproduces the CLI's size-11 and size-12 CNF hashes;
  - `scripts/recheck13.py` regenerates every CNF and compares hashes (`size13/recheck_nodrat.log`: OK).

Three things are argued and tested, but not formally proved:
1. **The tool's encoding and normalization** (tool README, "Soundness arguments", items 1, 2,
   4 and 5). Every circuit with at most 13 gates normalizes to an NF circuit with exactly s
   gates for some s ≤ 13, and every NF circuit satisfies the size-s CNF. The tool's
   validation suite tests this: 20698 checks against brute force, RAW mode and four
   independent encoders, with 0 failures. This is the same trust base as every other
   circuit_synth UNSAT bundle.
2. **The symmetry lemma** below, used to fix the first gate. It has a short proof, written
   below. It was also tested on 4 small 2-transitive Boolean-sum systems at every size up to
   the minimum or beyond, and on Fano at sizes 14 and 15 (`split_validation/validate_split.log`:
   all ok).
3. drat-trim itself, and the kissat 4.0.4 / drat-trim builds in `tool-circuit-synth/third_party`.

## The size-13 case split

Variables of the base CNF: gate 0 has one-hot selectors A[0][w] (var 1 + w) and B[0][w]
(var 8 + w) over the 7 inputs. Its op bit (true = AND) is var 27. The NOT bits isnot[j],
j = 0..12, are vars 28, 444, 864, 1288, 1716, 2148, 2584, 3024, 3468, 3916, 4368, 4824 and 5284.

**Symmetry lemma.** If the size-13 NF instance has a model, then it has one whose gate 0 is
NOT(x0), OR(x0,x1) or AND(x0,x1). The corresponding cubes are {A0=0, B0=0}, {A0=0, B0=1, AND
bit false} and {A0=0, B0=1, AND bit true}.

*Proof.*
- Let C be the NF list of a model. Gate 0 reads only inputs, so it is NOT(x_a) or OP(x_a,x_b)
  with a < b.
- The automorphism group of the Fano plane has order 168 and is 2-transitive on points
  (checked by enumeration in `validate_split.py`). So some automorphism σ has σ(a) = 0, or
  {σ(a),σ(b)} = {0,1}.
- Rename every input i to σ(i). Each line output becomes the output of line σ(L), and the set
  of seven lines is σ-invariant, so the output selectors can be reassigned.
- Every NF condition except the greedy order still holds:
  - correctness on all 128 rows, since σ permutes the rows;
  - pairwise distinct, non-constant row vectors that differ from the inputs;
  - "used", "relevant", at most one NOT, and exactly 13 gates.
- Re-sort the list greedily (tool README, soundness item 2). Keys then strictly increase, and
  the new gate 0 is the input-only gate of least key (b, a, op).
- The renamed list contains NOT(x0), with key (0,0,·) (the least possible key), or OP(x0,x1),
  with key (1,0,op). The only keys at most (1,0,AND) are NOT(x0), OR(x0,x1) and AND(x0,x1). ∎

**NOT-position split** (propositional). For the cubes OR(x0,x1) and AND(x0,x1), the
sub-cases are: all isnot[j] false, or isnot[p] true for some p in 1..12. In that cube,
isnot[0] is false by the base clause (¬isnot0 ∨ ¬A0[0] ∨ B0[0]) and the one-hot ladder of
B0. So the 1 + 2×13 = 27 cubes cover every model. Hence all 27 cases UNSAT ⇒ base CNF UNSAT.

## Results

Base CNF `size13/base_size13.cnf.xz`: 15912 vars, 113502 clauses, SHA-256
`ee9e1e53ca0c0a024b23449f1b0d5ef5a76eb5ae9bb1ada01128a27884ee3b3b` (same size as the earlier
uncertified run).

All 27 cases: kissat `s UNSATISFIABLE`, drat-trim `s VERIFIED`. One core each, three in
parallel, 4-core machine, 07:11 to 07:41 UTC on 2026-11-24. Total kissat time 1558 s,
drat-trim 2084 s, proofs 3.27 GB as text DRAT. The per-case CNF and proof SHA-256 values,
commands and drat-trim output are in `size13/results/<case>.json`.

| case | kissat s | drat-trim s | proof MB | stored |
|---|---|---|---|---|
| not_x0 | 226 | 278 | 452 | hash only |
| or_x0x1_nonot | 443 | 572 | 854 | hash only |
| and_x0x1_nonot | 357 | 459 | 712 | hash only |
| or_x0x1_not01..12 | 49, 45, 41, 42, 40, 25, 13, 20, 20, 15, 1, 1 | 62, 61, 56, 52, 57, 35, 24, 32, 34, 27, 1, 1 | 4–105 | .xz |
| and_x0x1_not01..12 | 60, 30, 38, 25, 15, 18, 9, 8, 9, 7, 2, 1 | 81, 42, 47, 35, 23, 28, 18, 17, 20, 16, 3, 1 | 4–145 | .xz |

The three proofs over 150 MB were deleted after hashing, as the tool did for MAJ5:

| case | proof SHA-256 |
|---|---|
| not_x0 | `332734c1996a4160…` |
| or_x0x1_nonot | `7684b50ffe10ce8e…` |
| and_x0x1_nonot | `8cf537ccbca4768e…` |

The full hashes are in the JSON files. To regenerate one, run
`kissat -q --no-binary case_<name>.cnf case_<name>.drat` with kissat 4.0.4, then
`drat-trim case_<name>.cnf case_<name>.drat -t 100000`. kissat is deterministic: re-runs on
three instances reproduced the recorded proof hashes byte for byte (`determinism/determinism.log`).

Sizes 1–12 (`sizes01-12/bundle.json`, made by the tool itself with
`none ... --size 12 --certify`, 11 min 49 s): every size is `s VERIFIED`, and
`proved_none_certified: true`.
- Size 12: kissat 255 s, drat-trim 297 s, 476 MB proof, hash only (`435c1cf978e43cb0…`).
- Size 11: 54 s / 70 s, 117 MB.

The other proofs are stored as .xz, and `circuit_synth_cli recheck sizes01-12` re-runs them.

## Layout

```
fano/
  CERTIFICATE.md            this file
  sizes01-12/               tool bundle: bundle.json, sizeNN.cnf.xz, sizeNN.drat.xz (no size12.drat)
  sizes01-12.log            the tool run
  size13/
    cases.json              spec, base hash, variable map, the 27 cubes and CNF hashes
    base_size13.cnf.xz      the tool's size-13 CNF
    case_*.cnf.xz           base + cube; case_*.drat.xz (24 stored proofs)
    results/*.json          per case: hashes, kissat/drat-trim commands, times, drat-trim output
    run.log, recheck_nodrat.log
  split_validation/         validate_split.log (lemma tests, coverage), coverage CNFs
  determinism/              kissat proof re-generation check
scripts/fano13_cases.py     builds base + case CNFs (imports circuit_synth)
scripts/run_cases.py        kissat + drat-trim per case
scripts/recheck13.py        regenerate CNFs, compare hashes, re-run drat-trim on stored proofs
scripts/validate_split.py   symmetry-lemma tests + coverage checks
```

**Independent recheck, done after packing.** Every CNF was regenerated from the encoder, every
hash matched, and drat-trim re-ran on every stored proof:
- `size13/recheck_full.log`: base and all 27 case CNFs match, and the 24 stored proofs give
  `s VERIFIED` again (13 min 24 s).
- `sizes01-12/recheck.log`: sizes 1–11 regenerated and `s VERIFIED`; size 12 has its CNF hash
  matching, and its proof is not stored (1 min 41 s).

Recheck commands:
- `tool-circuit-synth/venv/bin/python scripts/recheck13.py fano/size13`: about 15 min with
  drat-trim. Add `--no-drat` for the hashes only.
- `tool-circuit-synth/circuit_synth_cli recheck fano/sizes01-12`.
