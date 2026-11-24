# L-gct-181: a 4 x 5 level space of dimension >= 8

Status: REFUTED (checker: ACCEPTED (refute), last line in check.log).

The four conditions of L-gct-181 (total sum, S_2, S_3, S_4 = sums of 1x1 ... 4x4
subpermanents) are word for word the hypotheses of the accepted L-gct-215
(lean/PEqualNP/Outside/L_gct_215.lean), which proves finrank <= 7. So dimension >= 8 is
impossible. The refutation file is L-gct-215's proof copied into namespace
PEqualNP.Outside.L_gct_181 (theorem renamed `bound215`), then
`rintro ⟨L, hL, h8⟩; have h := ...bound215 L hL; omega`.
- File: lean/PEqualNP/Outside/L_gct_181.lean (copy here: L_gct_181.lean, 7568 lines;
  `lake env lean` takes about 11 minutes, compile.log has only linter warnings).
- Check: `node tools/check-lean.mjs lean/PEqualNP/Outside/L_gct_181.lean <this>/statement.lean refute`.

## Relation to L-gct-219
Same object: on 4 x 5 matrices, sum over injections of prod (1 + t) = 120 + 24 S_1 + 6 S_2
+ 2 S_3 + S_4, so "= 120 on L" is exactly "S_1 = ... = S_4 = 0 on L" (homogeneity).
L-gct-219 says no 7-dim space; L-gct-215 says <= 7; the record has 6.
Numerics for dimension 7 (see ../L-gct-219/README.md): not found.
