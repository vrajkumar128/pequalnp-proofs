# L-meta-1045: computational evidence (not a proof)

Status: not proved (missing lemma). The statement looks true.

## On paper
- Every wire reached from the output is thin (formal catch: gate inputs naming later or missing wires
  read false at evaluation but the classification uses final values).
- Each edge has a reached path to a leaf (an input of the edge, or a fat AND accepting it); leaves are at
  most 1 + reached thin ORs, giving 2D >= 2*tau - 2 - 2*sum_f(tau(E_f) - 1) over non-star fat leaves f.
- Missing: A + B >= |E| + sum_f(2*tau(E_f) - 3) (equality on the net graph). A null AND feeding the top
  thin-OR tree is never fat (else G contains K_{2,2}).

## Computer evidence (programs and outputs in search/)
- Exhaustive search of reduced two-input AND/OR circuits against all labeled C4-free graphs, des chosen to
  minimise Fz; validated by recovering optimal circuits.
  - n <= 5: even the old count A+B+2D is never beaten.
  - n = 6, A+B+2D <= 10: the old count fails only on the net graph (triangle 0,2,4 with pendants 1,3,5),
    e.g. (x0|x3|x4) & ((x0|x2|x5) & (x2|x4|x0x1)), 9 against 10; all 1087 such circuits have exactly one
    reached non-star fat AND, so the new count holds with equality.
  - n = 7, cost <= 10: 14025 circuits beat the old count (all on net plus a pendant); Fz restores it in
    every case.
- Recursive constructions over all 3839 C4-free graphs on 10 vertices and smaller: the old count is beaten
  by at most 1 (always via a top-level product); the new count is never beaten.
