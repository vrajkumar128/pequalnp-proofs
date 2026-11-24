# followup-onenot: can one NOT gate save a gate on the line-ORs of a projective plane?

This is self-directed follow-up work to L-meta-957. It made no desk calls and no git changes.

- `fano/CERTIFICATE.md` (task A): a DRAT-certified version of the Fano (q = 2) result. No
  fan-in-2 AND/OR/NOT circuit with at most one NOT gate and at most 13 gates computes the 7
  line-ORs, so 14 = 7·2 is the minimum.
- `order3/README.md` (task B): the PG(2,3) k = 5 K-local cases with one deficit flag fixed by
  Stab(K). This part is uncertified CEGIS, and every result is recorded with its cap.

```
followup-onenot/
  README.md
  fano/
    CERTIFICATE.md          what is certified, what rests on the encoding, hashes, timings
    sizes01-12/ (+ .log)    circuit_synth certified bundle for sizes 1..12 (+ recheck.log)
    size13/                 27-case split of size 13: cases.json, CNFs, 24 proofs (.xz), results/*.json
    split_validation/       symmetry-lemma tests and coverage checks
    determinism/            kissat proof-regeneration check
  order3/
    README.md               setting, soundness of the flag fixing, results
    run.log, logs/, sweep/  job logs
  scripts/                  fano13_cases.py, run_cases.py, recheck13.py, validate_split.py,
                            kloc5.py, run_kloc.py, sweep.sh
```

The scripts use `../tool-circuit-synth` (the encoder, kissat 4.0.4, drat-trim, and the venv
with python-sat) and `../L-meta-957/search957.py`, neither of which was modified.
