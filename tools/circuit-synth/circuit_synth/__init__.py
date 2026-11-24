"""circuit_synth: exact synthesis of small fan-in-2 Boolean circuits (AND/OR, AND/OR with at
most k NOT gates, AND/OR/NOT) with the semantics of PEqualNP.CircuitLowerBounds, with
certificates (Lean-semantics re-evaluation, Lean `decide` files, DRAT proofs checked by
drat-trim)."""
from .core import Circuit, Basis, Target, lean_eval, lean_wires, circuit_tables
from .encode import SB
from .synth import Problem, minimum, find, prove_none, VERSION
