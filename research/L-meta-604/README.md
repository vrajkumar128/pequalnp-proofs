# L-meta-604: XOR with a fresh input, checked on every function of at most 3 inputs

Step L-meta-604 claims, for every non-constant g on n inputs and every s:
y XOR g has a circuit of size s + 4 iff g or NOT g has a circuit of size s
(AND, OR and NOT gates of fan-in at most two, every gate counted, as in `HasCircuitSize`).
Equivalently: C(y XOR g) = min(C(g), C(NOT g)) + 4.

## Result

No counterexample for n <= 3. For every non-constant g on 1, 2 or 3 inputs, taken up to
permutation of the inputs (2 + 10 + 78 = 90 classes), the exact sizes satisfy
C(y XOR g) = min(C(g), C(NOT g)) + 4. The largest case is g = XNOR3 (0x69) and g = XOR3 (0x96):
C(g) = 8, and C(y XOR g) = 12, which is Redkin's 4(n - 1) for parity of 4 inputs.

The sizes are exact minima found by `circuit_synth_cli min --basis full`. That command searches
upward until the CNF for some size is satisfiable, and checks the circuit it finds against the
Lean semantics on every input. The lower halves (UNSAT at size - 1) were not DRAT-certified in
this run; `--certify` adds drat-trim certificates if wanted.

Note that C(g) and C(NOT g) differ by 1 in either direction for many g (for example 0x9:
C(g) = 6, C(NOT g) = 5), so the min in the statement matters.

## Files

- `xor_test.py`: the driver (enumerates classes, calls the tool, prints one line per class).
- `run.log`: one line per class: C(g), C(NOT g), C(y XOR g), min + 4.
- `sizes.json`: every exact size computed, keyed by [n, truth table]. The truth-table bit t is the
  value at the input with x_i = bit i of t, and y is the last input.

Reproduce, from the scratchpad:
`python3 -I L-meta-604/xor_test.py tool-circuit-synth/circuit_synth_cli L-meta-604/sizes.json 3`
