# Refutations of L-gct-181 and L-gct-182

Both files are accepted by `node tools/check-lean.mjs <file> <statement> refute`.
They are not sent as pull requests: the authoritative check runs only in check mode, and the
negated twins of these search steps are already merged:

- L-gct-181 asks for a 4 x 5 level space of dimension at least 8. Its four conditions are word for
  word the hypotheses of the merged L-gct-215, which proves dimension at most 7.
  `L_gct_181.lean` copies the proof of L-gct-215 into its own namespace and closes with omega.
- L-gct-182 asks for a 4-dimensional doubly centred level space at 4 x 4. The merged L-gct-216
  proves dimension at most 3 under the same conditions; `L_gct_182.lean` reuses that proof.

So both search steps are settled by results already on main; the desk still lists them as open.
