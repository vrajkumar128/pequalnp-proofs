# circuit_synth: exact synthesis of small Boolean circuits, with certificates

`circuit_synth` finds minimum fan-in-2 circuits for small Boolean functions, or proves that none
of a given size exists. It is useful to anyone studying small-circuit complexity, whatever
happens to P vs NP.

- **Semantics.** The circuit model is exactly that of the pequalnp.com Lean library
  (`PEqualNP.CircuitLowerBounds.Circuit`, `FanInTwo`, `HasCircuitSize`, `Monotone2`).
- **Targets.** A truth table (any function, n up to about 12), a graph edge function, Boolean
  sums and other multi-output families (the outputs share gates), and a monotone function given
  by minterms (optionally checked against its maximal false points).
- **Bases.** AND/OR (monotone), AND/OR with at most k NOT gates, and AND/OR/NOT, all with fan-in
  at most 2.
- **Queries.** Find a circuit of size ≤ s, prove that none of size ≤ s exists, or find the
  minimum. Side constraints let you state desk-style shards:
  - fixed first gates;
  - "some AND gate is true on row r", or "no AND gate is true on row r";
  - gate-elimination bounds.
- **Certificates.**
  - SAT answers: an exact re-evaluation on all 2^n inputs with a copy of the Lean semantics,
    and a Lean 4 file that proves the circuit correct with `decide` (no `native_decide`).
  - UNSAT answers: DRAT proofs (kissat or CaDiCaL) checked by drat-trim, with SHA-256 hashes
    of the CNF and the proof, and a `recheck` command that regenerates the CNF from the recorded
    spec.
- **Validation.** `circuit_synth validate` checks the tool against brute force, against known
  values, and against the four encoders it was merged from (results below).

```
tool-circuit-synth/
  circuit_synth_cli          wrapper: runs `python -m circuit_synth` with the bundled venv
  circuit_synth/
    core.py                  Circuit, exact Lean evaluator, Basis, Target (+ constructors)
    encode.py                CNF encodings NF and RAW, side constraints, decoding
    synth.py                 Problem, find / prove_none / minimum, verification, bundles
    solve.py                 python-sat (in-process), kissat / cadical (DRAT), drat-trim
    lean.py                  Lean 4 certificate emitter
    brute.c                  exhaustive enumeration used by the validation suite
    validate.py              the validation suite
    cli.py                   command line
  reference/                 the merged encoders, unchanged (onenot_search.py, junk_shard.py,
                             shard_search.py, synth2.py + its graphs.py, probe20.lean), used by `validate`
  scripts/build_tools.sh     builds kissat 4.0.4, CaDiCaL 2.1.3 and drat-trim into third_party/bin
  scripts/examples.sh        regenerates examples/ (certified runs + Lean files) with timings
  scripts/pack_examples.sh   xz-compresses the example CNFs and proofs (recheck reads .xz)
  scripts/bench.py           the timings below
  third_party/bin/           solver and checker binaries (not committed)
  examples/                  certificate bundles (bundle.json, CNFs, DRAT proofs) and Lean files
  validation/                logs and JSON summaries of the validation runs
```

## Install

```
scripts/build_tools.sh                      # kissat, cadical, drat-trim -> third_party/bin
python3 -m venv venv && venv/bin/pip install python-sat   # optional, faster uncertified runs
./circuit_synth_cli -h
```
Without python-sat the tool calls kissat for every instance. Solver paths can be overridden
with `CIRCUIT_SYNTH_KISSAT`, `CIRCUIT_SYNTH_CADICAL` and `CIRCUIT_SYNTH_DRAT_TRIM`.

## Usage

```
# minimum monotone circuit for the edge function of the path P4 (answer 4)
./circuit_synth_cli min --graph 0-1,1-2,2-3 --basis mono
# the same, with a Lean certificate and a certificate bundle (every smaller size DRAT-checked)
./circuit_synth_cli min --graph 0-1,1-2,2-3 --basis mono --certify --out runs/P4 --lean P4.lean
# prove that no monotone circuit with at most 6 gates computes the C5 edge function
./circuit_synth_cli none --graph 0-1,1-2,2-3,3-4,4-0 --basis mono --size 6 --out runs/C5
./circuit_synth_cli recheck runs/C5          # regenerate the CNFs, compare hashes, re-run drat-trim
# truth tables: hex (bit t = value on the input with x_i = bit i of t) or a 0/1 string
./circuit_synth_cli min --n 3 --tt 0x96 --basis knot=1        # XOR3 with at most one NOT: 9
./circuit_synth_cli min --n 3 --tt 0x96 --basis full          # XOR3, AND/OR/NOT: 8
# multi-output: Boolean sums, or a list of truth tables
./circuit_synth_cli min --sums "0,1,2;1,2,3;0,3" --basis mono
./circuit_synth_cli min --n 3 --tables 0x96,0xe8 --basis full
# monotone target by minterms (with an optional check of its maximal false points)
./circuit_synth_cli min --minterms "0,1;1,2;2,3" --maxfalse "0,2;0,3;1,3" --basis mono
# find a circuit with at most s gates; prove none with at most s gates
./circuit_synth_cli find --graph 0-1,1-2,2-3,3-4,4-0 --basis mono --size 8
./circuit_synth_cli none --n 3 --tt 0x96 --basis full --size 7 --certify   # --out implies --certify
# side constraints (shards)
./circuit_synth_cli min --graph 0-1,1-2,2-3 --basis mono --prefix "and:0,1"
./circuit_synth_cli none --graph ... --basis mono --size 9 --exists "and@{0,2,3}"   # class claim, see 7.
./circuit_synth_cli min --graph ... --basis mono --forbid "and@{0,2,3}"   # no AND gate true there
./circuit_synth_cli min --graph ... --basis mono --restrict "P=0;L=auto" --restrict "Q=4;L=auto"
# DIMACS only
./circuit_synth_cli dimacs out.cnf --graph 0-1,1-2,2-3 --basis mono --size 3
./circuit_synth_cli validate [--quick] [--sections known,brute3,...] [--out DIR]
```

Options: `--basis mono|full|knot=K` · `--mode nf|raw` · `--sb all|none|used,distinct,order,relevant`
· `--rows auto|full|minterm` (`auto` uses minterm rows for graph, sums and minterm targets in the
monotone basis) · `--solver kissat|cadical` (certified runs) · `--backend auto|pysat|kissat|cadical`
(uncertified runs) · `--timeout SEC` · `--json`.

Python:
```python
from circuit_synth import Target, Basis, Problem, minimum, prove_none, SB
from circuit_synth.lean import emit
t = Target.graph(5, [(0,1),(1,2),(2,3),(3,4),(4,0)]).monotone_rows()
r = minimum(Problem(t, Basis(0)), smax=10)          # r['min_size'] == 7, r['_circuit']
open('C5.lean', 'w').write(emit(r['_circuit'], t, Basis(0), name='C5'))
prove_none(Problem(t, Basis(0)), 6, certify=True, workdir='runs/C5')
```

## Semantics (copied from `Defs/CircuitLowerBounds.lean`)

Inputs are wires `0..n-1` and gate `j` is wire `n+j`. A gate reads wires by index. An index
that does not exist yet reads `false`; this includes the gate's own index and any later gate.
`AND [] = true` and `OR [] = false`. `NOT` reads only its first input, and `NOT [] = true`.
The output index may point anywhere, and a missing output wire reads `false`.
`core.lean_wires` / `core.lean_eval` copy `Circuit.wires` / `Circuit.eval` line by line. Every
circuit the tool reports is re-evaluated with them on all 2^n inputs.

Conventions in the answers: constant false has size 0 (the output points at a missing wire).
Constant true needs one gate (`AND []`), and one such gate can serve several outputs. A
projection x_i has size 0. Truth tables use `tableIndex`: row t is the input with x_i = bit i of t.

In the Lean files, a multi-output circuit is one shared gate list with one `Circuit` per output.

## Encodings

### NF (normal form, default)

Each of the s gates (after any fixed prefix) has:
- one-hot selectors `A[j][w]`, `B[j][w]` for its smaller and larger input, with ladder (order)
  variables `a_j ≥ i`, `b_j ≥ i`;
- an op bit (AND/OR) and a NOT bit;
- per-row values `v`, `va`, `vb`.

The inputs satisfy `a ≤ b`. `a = b` holds exactly for a NOT gate. Without NOT, `a < b`. Per
gate and row, the CNF has 4 clauses per available wire plus 8 for the gate function, so its size
is O(s·(n+s)·R) for R rows. This is the A/B layout of L-meta-1342/1343 (encoding B), which scales
to full truth tables with n ≈ 10. Outputs: with one output and no prefix, the output is the last
gate; otherwise each output has a one-hot selector over the gates (and over fixed gates that
already compute it).

Optional symmetry breaking (`--sb`, default all four):

| flag | constraint |
|---|---|
| `used` | every gate is read by a later gate or is an output |
| `distinct` | the row vector of every gate differs from that of every earlier wire (inputs, fixed gates, gates) and from both constants |
| `order` | greedy topological order: the key (b, a, op), with OR < AND and NOT having a = b, strictly increases along the free gates (all pairs). When one output is fixed at the last gate and `used` is off, the last gate is left out (see 2.) |
| `relevant` | every input that some output depends on is read by some gate |

### RAW (every Lean gate, no normal form)

Gate j is op(src1, src2), where op is AND, OR or NOT and each source is a wire `0..n+j-1`,
TRUE or FALSE. TRUE means the input is omitted from an AND. FALSE means a missing wire, or the
input is omitted from an OR or a NOT. An OR or NOT gate with a TRUE source is forbidden, since
no Lean gate is like that. So the RAW gates are, semantically and op for op, exactly the
`FanInTwo` gates:
- `AND []`, `AND [x]`, `AND [x,y]` and `AND [missing]`;
- `OR []`, `OR [x]` and `OR [x,y]`;
- `NOT []`, `NOT [x]` and `NOT [x, y]` (the second input is ignored).

Outputs select any wire or a missing one. RAW has no symmetry breaking and no normalization, so
it is the reference the NF arguments are tested against. It is slow beyond about 6 gates.

## Soundness arguments

Let C be any `FanInTwo` circuit (in the chosen basis) with s gates whose outputs agree with the
targets on the encoded rows R. For full truth tables R is all of {0,1}^n.

1. **Normalization.**
   - Replace every gate by its value as a function of at most two existing wires and the
     constants. A missing wire is the constant false, `AND []` is true, and so on.
   - Repeat until nothing changes:
     - (a) A gate whose row vector on R is constant is deleted. Its readers get the constant
       and simplify: AND(1,y) = y, AND(0,y) = 0, OR(0,y) = y, OR(1,y) = 1, NOT(c) = ¬c.
     - (b) A gate whose row vector equals that of an earlier wire w is deleted, and its readers
       and outputs are redirected to w. A copy gate (`AND [x]`, `AND [x,x]`, `OR [x]`, ...) is a
       special case.
     - (c) A gate that is neither read nor an output is deleted.

   Every step keeps the values of all remaining wires on R and never adds a NOT gate. Each step
   lowers the size by one, so the loop ends.

   At the end every gate is AND/OR of two distinct wires or NOT of one wire. All row vectors are
   pairwise distinct and non-constant, and every gate is used. A non-trivial output (not a
   constant or a projection, see 5.) cannot end on an input or be constant, so it is a gate.
   With one output, the output gate is then the only gate nobody reads, so it is last in every
   topological order.
2. **Greedy order** (Knuth / Kojevnikov–Kulikov style).
   - Order the gates by repeatedly placing the available gate with the smallest key
     (b, a, op), using the current numbering.
   - When a gate is placed at wire p, the gates that become available read p. Their b = p is
     larger than the b of every gate that was available before, and those keys were all at
     least the key just placed. So the keys never decrease.
   - Two gates with equal keys compute the same function, which (b) excluded. So the keys
     strictly increase.

   Reordering keeps 1. With one output, the representation fixes the output at the last
   gate. That gate is the only sink only when every gate is used. So when `used` is off, the
   ordering constraint covers just the gates before the output. The validation suite found
   that this restriction is needed: with `--exists` and `--sb order,relevant`, an unused gate
   could otherwise be ordered after the output.
3. **Relevant inputs.** A correct circuit for a function that depends on x_i reads x_i. In the
   minterm-row case this still holds, because of the sufficiency argument below.
4. Hence every circuit with s gates yields an NF circuit with s' ≤ s gates satisfying every
   flag. **An NF instance is "exactly s' gates"**, so `none ≤ s` and `minimum` check every size
   from the lower end up to s, and `prove_none` certifies each of those sizes separately.
   In RAW, any circuit with fewer gates can be padded with `AND []` gates without changing
   anything. With `--forbid`, it is padded with `OR []` gates instead. So a single RAW size
   covers "≤ s", unless `--exists` is used.
5. **Trivial outputs** are handled outside the SAT instance:
   - constant false: a missing wire, 0 gates;
   - a projection: the input wire, 0 gates;
   - constant true: one `AND []` gate, shared by all such outputs, unless a fixed gate already
     is constant true.

   Since NF gates are never constant, the minimum is (NF minimum for the non-trivial outputs)
   plus 1 if some output is constant true. Repeated output functions share one wire.
   The appended `AND []` gate is outside the NF class, so the tool refuses a constant-true
   output together with `--exists` or `--forbid` in NF mode. Use `--mode raw` there.
6. **Sufficiency of minterm rows (monotone basis only).**
   - Let f be monotone and let g be computed by a monotone circuit with g(m) = 1 for every
     minterm m of f and g(p) = 0 for every maximal false point p.
   - If f(x) = 1, then x ≥ m for some minterm m, so g(x) ≥ g(m) = 1.
   - If f(x) = 0, then x ≤ p for some maximal false point p, so g(x) ≤ g(p) = 0.
   - So g = f.

   Normalization 1 is applied relative to R. It may change values off R, but the result is
   still a monotone circuit that is correct on R, hence correct everywhere. The tool refuses
   minterm rows in any basis with NOT gates, where the argument fails. For a graph edge
   function the minterms are the edges and the maximal false points are the maximal
   independent sets, as in L-meta-1342/1343.
7. **Side constraints.**
   - *Fixed prefix.* Normalization and ordering are applied to the free suffix only. Fixed
     gates are wires with known values; a suffix gate may not duplicate one.
   - *Gate elimination* (`--restrict P;Q;L`). Every circuit C of size s computing f satisfies
     the constraint, so it removes no circuit and is sound with every flag. Under x_P = 1,
     x_Q = 0, a gate with an input that is constant on the subcube becomes a constant or a copy
     and can be deleted. The rest computes f restricted, which needs at least L gates, so at
     most s − L gates have a constant input.
     - Monotone basis: a wire is constant 1 iff it is 1 at the least point of the subcube, and
       constant 0 iff it is 0 at the greatest point. Two rows suffice (the L-meta-1342/1343
       clauses).
     - Otherwise: the whole subcube is encoded.

     L must bound only the gates that are not eliminated. An output that becomes constant
     true under the restriction is itself an eliminated gate, so it costs nothing here and
     needs no `AND []` gate. `L=auto` is therefore the minimum size of the restricted function
     in the same basis, computed by the same tool, minus the one `AND []` gate that the minimum
     charges for constant-true outputs. With `--certify`, its UNSAT sizes are certified too, in
     sub-bundles. The validation suite found this subtraction is needed: for ¬x0 ∨ x2 under
     x0 = 0, both gates have a constant input.
   - *"Some OP gate is true on row r"* (`--exists`). This is a property of the gate list, and
     normalization may delete the witness. For example, an AND gate can duplicate an OR gate,
     and in raw Lean `AND []` is true on every row. So such a constraint defines a class.
     - An UNSAT answer means: no circuit of the encoded class satisfies it.
     - For NF with `--sb none` or `--sb order,relevant`, the class is "exactly s nondegenerate
       gates, output last". Reordering and relevance keep every gate, so the answer covers
       that whole class.
     - `used` and `distinct` shrink the class. Use them with `--exists` only with an argument
       of your own (as L-meta-1342 did for its junk-AND shards).

     The validation suite compares `--exists` with an exhaustive enumeration of that class.
   - *"No OP gate is true on row r"* (`--forbid`). Normalization never adds a gate. A
     surviving gate keeps its op, and its values on R, where r is added to R. So this property
     survives normalization, and the claim covers every circuit, with every flag. RAW pads with
     `OR []`, which is never true, so a single RAW size again covers "≤ s". Tested against the
     enumeration with every configuration and with RAW.

## Certificates

**SAT.**
- The model is decoded into a Lean gate list. `Problem.verify` re-evaluates it with the Lean
  semantics on all 2^n inputs, then checks the basis (fan-in, NOT count), the size, the prefix
  and the side constraints.
- A failed verification aborts the run; it never happened in validation.
- `--lean FILE` emits a file that defines `gates` and `C0, C1, ...`, then proves:
  - `FanInTwo` (`simp`), `Monotone2` for the monotone basis, and the NOT count by `decide`;
  - `tabK : ∀ b0 … b(n-1), CK.eval [b0, …] = spec` by `decide`;
  - `mainK : HasCircuitSize n spec s`.

  For a multi-output target it also proves `shared`.
- The spec is the target's formula (graphs, sums, minterms) or `tableFun n T` with the explicit
  table T.
- Compile with `cd /home/user/pequalnp-proofs/lean && ~/.elan/bin/lake env lean FILE`.
- Small files take about 5 s. L-meta-651's 20-gate, 10-input file took about 75 s.

**UNSAT.** With `--certify` or `--out`, each UNSAT size is solved by kissat
(`--no-binary`, or CaDiCaL) with a text DRAT proof, and checked with `drat-trim CNF PROOF`.
`bundle.json` records:
- the spec;
- for each size: the status, variables and clauses, the CNF and proof SHA-256, the drat-trim
  verdict, and timings;
- `all_unsat_certified` and `proved_none_certified`.

The CNF header comments carry the canonical spec. `circuit_synth recheck DIR` rebuilds every CNF
from it, compares hashes and re-runs drat-trim.

**Examples** (`examples/`, made by `scripts/examples.sh`; CNFs and proofs xz-compressed):

| bundle | certifies |
|---|---|
| `P4_mono_min` | P4 edge fn: minimum monotone size 4 (sizes 1–3 DRAT, circuit + `P4.lean`) |
| `maj3_mono_min` | majority-3: monotone minimum 4 (+ `maj3.lean`) |
| `xor2_onenot_min` | XOR2 with ≤ 1 NOT: minimum 4 (+ `xor2.lean`) |
| `xor3_onenot_min` | XOR3 with ≤ 1 NOT: minimum 9 (+ `xor3.lean`) |
| `xor3_full_min` | XOR3 in AND/OR/NOT: minimum 8 (+ `xor3.lean`) |
| `sums_min` | Boolean sums x0∨x1∨x2, x1∨x2∨x3, x0∨x3: 4 shared gates (+ `sums.lean`) |
| `C5_mono_min` | C5 edge fn: monotone minimum 7 (+ `C5.lean`) |
| `C5_mono_none6`, `C5_mono_none6_raw` | no monotone circuit with ≤ 6 gates for C5, in NF (6 sizes) and in RAW (one instance) |
| `P4_mono_none3_raw` | no monotone circuit with ≤ 3 gates for P4, in RAW |
| `MAJ5_mono_none9` | no monotone circuit with ≤ 9 gates for MAJ5 (3 of 5), with minterm rows. `maj5.lean` there proves a 10-gate monotone circuit, so the monotone minimum is 10. The size-9 DRAT proof (225 MB) is not stored. Its SHA-256 is in `bundle.json`, and kissat, which is single-threaded and deterministic, regenerates it. |

All `.lean` files compile in about 5 s each.

**What an UNSAT certificate establishes, and what it does not.** drat-trim certifies that the
CNF file is unsatisfiable. That is all.

The step from "these CNFs are UNSAT" to "no circuit with ≤ s gates computes f" also rests on:
1. the encoding being a faithful description of the NF (or RAW) class, which is Python code;
2. the normalization and symmetry-breaking arguments above;
3. for minterm rows, the sufficiency argument;
4. for `L=auto` restrictions, the certified minimum of the restricted function;
5. that every size from the lower end to s was checked.

None of these is formally verified. Items 1, 2 and 4 are tested by the validation suite. RAW
mode removes item 2, at a large cost in speed. A Lean proof of a lower bound would need to
reflect the CNF and the encoding in Lean, which this tool does not do.

## Validation (`circuit_synth validate`)

See [validation results](#validation-results) for the recorded runs.

- **known**: known minimum sizes, all in NF (minterm and full rows, `sb` all/none) and in RAW
  where feasible:
  - monotone graph edge functions: P4 = 4, K_{1,3} = 3, C4 = 3, K3 = 4, P5 = 5, C5 = 7;
  - majority-3 = 4 in all three bases;
  - XOR2 = 4 with ≤ 1 NOT, ≤ 2 NOT and full, and no monotone circuit with ≤ 6 gates;
  - XOR3: the full-basis minimum is at most the one-NOT minimum. The values themselves
    (9 with ≤ 1 NOT, 8 with AND/OR/NOT) are DRAT-certified in `examples/`;
  - constants and projections, and Boolean sums.
- **brute3**: all 256 functions of 3 inputs in all four bases (mono, ≤ 1 NOT, ≤ 2 NOT, full).
  Every symmetry-breaking configuration (all, none, each flag alone, each flag left out) is
  compared with `brute.c`, an exhaustive enumeration whose only pruning is "skip a gate equal to
  an existing wire". The cap is 7 gates.
- **brute4**: all 166 non-constant monotone functions of 4 inputs, monotone basis, full rows and
  minterm rows, every configuration, against brute force (cap 7, which covers all of them).
- **graphs**: all 64 labelled graphs on 4 vertices with minterm rows, against brute force, in
  the monotone and ≤ 1 NOT bases. Random non-monotone 4-input functions (≤ 1 NOT and full,
  cap 6) are compared too.
- **raw**: RAW (every Lean gate) = NF = brute force on all 3-input functions in three bases, up
  to 5 gates, including constants.
- **sums**: Boolean sums and random multi-output families against brute force (multi-target
  mode).
- **reference**: agreement with the merged encoders:
  - `onenot_search` on all 3-input functions, with and without its symmetry breaking;
  - `junk_shard` and `shard_search` (encodings A and B) on all graphs up to 5 vertices up to
    isomorphism;
  - `synth2` (AND/OR/NOT, cap 9) on the same graphs. The dense 5-vertex graphs need more
    than 9 gates in that basis, so this part takes about 30 minutes.
- **restrict**: gate-elimination constraints with automatic bounds (x_v = 1 and x_v = 0 for
  every v) never change the minimum, on all graphs up to 5 vertices and random 3-input
  functions (NF and RAW).
- **exists**: `--exists and@r` against an exhaustive enumeration of the NF class (n = 3 full
  basis and n = 4 monotone, up to 4 gates).
- **forbid**: `--forbid and@r` against an exhaustive enumeration of minimum sizes, in several
  configurations and in RAW.
- **prefix**: fixing the first gate of a minimum circuit keeps the minimum, and fixing a useless
  copy gate adds exactly one.
- **certs**: certified `none` runs with both solvers, all checked by drat-trim. A negative test
  checks that an UNSAT proof is rejected against a satisfiable CNF.
- **lean** (run with `--sections lean`): emitted files compile with `lake env lean`:
  majority-3, P4, XOR2 with one NOT, a 3-output Boolean sum, and a 10-gate MAJ5 circuit stated
  with `tableFun 5`.

## Validation results

These are the full runs of 2026-11-24 (logs and JSON in `validation/`):
- `full_A`: known, brute3, brute4, graphs;
- `full_B`: raw, sums, reference, restrict, exists, forbid, prefix, certs;
- `lean`.

`full_C` is an independent rerun of B's last five sections, with identical counts and no
failures. Part A and part B ran in parallel, one core each.

| section | checks | failures | time |
|---|---|---|---|
| known | 60 | 0 | 5 s |
| brute3 (256 functions × 4 bases × 10 configurations, cap 7) | 7800 | 0 | 252 s |
| brute4 (166 monotone functions × 2 row sets × 10 configurations, cap 7) | 3320 | 0 | 29 s |
| graphs (64 labelled 4-vertex graphs; 120 random 4-input functions) | 795 | 0 | 46 s |
| raw (RAW = NF = brute force, all 3-input functions, 3 bases, cap 5) | 532 | 0 | 20 s |
| sums (Boolean sums and multi-output families vs brute force) | 68 | 0 | 69 s |
| reference (onenot: all 3-input functions; junk_shard, shard_search A and B, synth2: all 46 graphs up to 5 vertices) | 716 | 0 | 1967 s |
| restrict (auto gate-elimination bounds never change the minimum; NF and RAW) | 166 | 0 | 210 s |
| exists (`--exists and@r` vs enumeration of the NF class) | 3600 | 0 | 5 s |
| forbid (`--forbid and@r`: 5 configurations and RAW vs enumeration) | 3520 | 0 | 11 s |
| prefix | 100 | 0 | 6 s |
| certs (DRAT with kissat and CaDiCaL + negative test) | 11 | 0 | 3 s |
| lean (5 emitted files compiled, no `native_decide`) | 10 | 0 | 60 s |
| **total** | **20698** | **0** | |

`validate --quick` (about 5 minutes) runs a reduced version of every section except lean.

**Two bugs found by the suite and fixed before the runs above.** Both made results too
strong, never too weak. `validation/quick_first_run_with_2_bugs.log` records them.

1. `L=auto` gate-elimination bounds charged one gate for a restricted function that is
   constant true. Example: ¬x0 ∨ x2 under x0 = 0. Such a bound is one too high and
   wrongly removes circuits. The fix is in soundness item 7.
2. `order` without `used` ordered the output gate together with the others. With unused gates
   allowed, a circuit may need an unused gate placed after the output, and the constraint
   excluded that. It only matters when unused gates cannot be deleted, as with `--exists`.
   Example: tt = 0xfafa with an AND gate on row 10. The fix is in soundness item 2.

Neither bug affected plain minimum or prove-none results: the brute-force sections passed
before and after the fixes.

## What was taken from the merged encoders

| source | taken |
|---|---|
| L-meta-1444 `onenot_search.py` | k-NOT budget, NOT as a = b, the distinct-functions constraint including inputs, the "used" constraint, cross-validation against brute force |
| L-meta-1342 `junk_shard.py` | A/B selector layout with ladders, all-pairs greedy order (b, a, op), relevant-input clauses, gate-elimination bound with an at-most-k counter, edge + maximal-independent-set rows, the junk-AND (`--exists`) shard constraint |
| L-meta-1343 `shard_search.py` | two-row restriction test for monotone wires, the dirty-row constraint, the Lean-semantics evaluator style, kissat 4.0.4 / CaDiCaL 2.1.3 builds |
| L-meta-519 `synth2.py` | AND/OR/NOT selectors with NOT as a = b, gate elimination in a basis with NOT (here: exact subcube constancy instead of structural propagation) |
| L-meta-651 `probe20.lean` | the Lean certificate pattern (`decide` over n Booleans, `List.ofFn` rewrite) |

New here: the RAW encoding of every Lean gate, multi-output and trivial outputs, the fixed prefix
in normal form, subcube constancy for restrictions with NOT, the certificate bundle with
recheck, and the Lean emitter for tables and several outputs.

## Limitations

- Exact synthesis is exponential.
  - Full truth tables up to n = 10 work when the circuits are small: about 10 gates in
    seconds to a minute.
  - Hard cases did not finish within minutes: XOR4 at 12 gates, and the 10-input Petersen
    edge function at 20 gates.
  - With minterm rows, monotone instances go further: the L-meta-1342/1343 shards had 11
    inputs and 21 gates, with hours of solver time.
  - UNSAT near the minimum is usually the expensive part.
- NF instances are "exactly s gates", and that is not monotone in s. For example, AND2 has no
  2-gate NF circuit. So `find --size s` tries s, s−1, …, and a size above the minimum can be
  slow or UNSAT.
- The shard constraints are position-free (`--exists`, `--forbid`), plus the fixed prefix and
  the elimination bounds. Constraints that depend on gate positions, like L-meta-1342's
  "the first junk AND is gate k", still need a custom encoder. `reference/junk_shard.py`
  shows the pattern.
- The tool only does fan-in ≤ 2 AND/OR/NOT. MOD and MAJ gates, unbounded fan-in and depth
  bounds are not encoded.
- An UNSAT certificate certifies the CNF, not the encoding (see above). There is no Lean
  reflection of lower bounds.
- `--exists` claims are relative to the encoded class (see 7.).
- `L=auto` recursion re-solves restricted functions without caching across runs.
- Lean `decide` time grows like 2^n · size. Beyond n ≈ 10, expect minutes.
- `brute.c` table mode needs n ≤ 4. Multi mode handles n ≤ 6 but is exponential in the cap.

## Timings

All runs used one core of a shared 4-core machine, wall clock. Uncertified solving used
python-sat CaDiCaL 1.9.5 unless kissat is named.

Certified end-to-end runs (`scripts/examples.sh`). Each includes encoding, kissat with a DRAT
proof, drat-trim for every UNSAT size, re-evaluation and the Lean file:

| run | answer | time |
|---|---|---|
| P4 edge fn, mono, `min --certify` | 4 | 0.3 s |
| majority-3, mono, `min --certify` | 4 | 0.3 s |
| XOR2, ≤ 1 NOT, `min --certify` | 4 | 0.3 s |
| XOR3, ≤ 1 NOT, `min --certify` | 9 | 2.3 s |
| XOR3, AND/OR/NOT, `min --certify` | 8 | 1.9 s |
| Boolean sums {012, 123, 03}, mono, `min --certify` | 4 | 0.3 s |
| C5 edge fn, mono, `none --size 6` (sizes 1..6, NF) | none | 1.7 s |
| C5 edge fn, mono, `none --size 6 --mode raw` (one RAW instance) | none | 3.0 s |
| C5 edge fn, mono, `min --certify` | 7 | 1.8 s |
| MAJ5 (3 of 5), mono, minterm rows, `none --size 9` (sizes 1..9) | none | 184 s (size 9: kissat with proof ≈ 65 s, 225 MB DRAT, drat-trim 106 s) |

Single sizes (`scripts/bench.py`):

| instance | size | answer | time | CNF |
|---|---|---|---|---|
| C5 edge fn, mono, minterm rows (10 rows) | 6 / 7 | UNSAT / SAT | 0.15 s / 0.20 s | 534 vars, 2.7k clauses |
| C5 edge fn, mono, full rows (32 rows) | 6 / 7 | UNSAT / SAT | 0.21 s / 0.15 s | 1.3k vars, 6.8k clauses |
| C5 edge fn, mono, RAW, minterm rows | 6 / 7 | UNSAT / SAT | 1.44 s / 0.13 s | 437 vars, 2.4k clauses |
| XOR3, ≤ 1 NOT | 8 / 9 | UNSAT / SAT | 0.31 s / 0.52 s | 688 vars |
| XOR3, AND/OR/NOT | 7 / 8 | UNSAT / SAT | 0.29 s / 1.53 s | 546 vars |
| MAJ5 (3 of 5), mono, minterm rows | 10 | SAT | 5.2 s | 1960 vars, 10.9k clauses |
| MAJ5 (3 of 5), mono, minterm rows, kissat | 9 | UNSAT | 66 s | 1647 vars, 9.0k clauses |
| 8-input 5-term DNF, full 256 rows, AND/OR/NOT, kissat | 8 / 9 | UNSAT / SAT | 17 s / 18 s | 14k vars, 95k clauses |
| 10-input 4-term DNF, full 1024 rows, AND/OR/NOT | 9 / 10 | SAT / SAT | 79 s / 23 s (encoding 0.4 s) | 65k vars, 484k clauses |
| same, mono, minterm rows (34 rows) | 9 / 10 | SAT / SAT | 3.8 s / 3.4 s | |
| XOR4, AND/OR/NOT, kissat | 12 | timeout | > 240 s | 2.2k vars, 12.7k clauses |
| Petersen edge fn (10 inputs), mono, minterm rows, kissat | 20 | timeout | > 420 s | 9.4k vars, 66k clauses |

The last two rows show where exact synthesis stops being practical. L-meta-651 found a
20-gate Petersen circuit by simulated annealing, but the exact search at 20 gates did not
finish in 7 minutes. A row like MAJ5 at size 9 is one size. The claim "minimum = 10" also
needs sizes 1–8, which are fast. `examples/MAJ5_mono_none9` certifies all of them (see below).

Lean: the emitted files for 2 to 5 inputs and up to 10 gates compile in about 5 s each
(`lake env lean`, most of it importing Mathlib). L-meta-651's 20-gate, 10-input file of the
same shape takes about 75 s.

Validation: see the per-section times in [validation results](#validation-results).
