# L-gct-182: four independent 4 x 4 doubly centred matrices spanning a level space

Status: REFUTED (checker: ACCEPTED (refute)).

The hypotheses of L-gct-182 are word for word the hypotheses of the accepted L-gct-216
(lean/PEqualNP/Outside/L_gct_216.lean), which proves every such space has finrank <= 3.
So no 4-dimensional one exists. The refutation file is L-gct-216's proof copied into the
namespace PEqualNP.Outside.L_gct_182 (its theorem renamed `bound216`), followed by

    theorem PEqualNP.Outside.L_gct_182 : ¬ (<statement>) := by
      rintro ⟨L, hL, hr⟩
      have h := PEqualNP.Outside.L_gct_182.bound216 L hL
      omega

- File: lean/PEqualNP/Outside/L_gct_182.lean (copy in this folder: L_gct_182.lean).
- Check: `node tools/check-lean.mjs lean/PEqualNP/Outside/L_gct_182.lean <this>/statement.lean refute`
  -> ACCEPTED (refute). Compile time about 2 minutes.

Numerics agree: 3000 Levenberg-Marquardt runs for dimension 4 in the 9-dim doubly centred
space never get below residual 0.37, while dimension 3 is found (cube-root-of-unity patterns
on three rows; ../L-gct-231/fast4.py 4 4 3 600 7 rc).
