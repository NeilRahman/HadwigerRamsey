# Four-colour component optimization

This development formalizes **Lemmas 2–4** of the local manuscript
`four_colour_analytic.tex`. It builds on the general component program in
`ComponentTransfer`. The manuscript is excluded from version control.

## Program and coordinates

`Program.lean` reuses `ComponentTransfer.ComponentInstance 4` as
`HadwigerRamsey4Col.ComponentInstance`, and defines `beta4` to be
`ComponentTransfer.beta 4`.

For the three-pairing pattern, `PairingData` gives the four masses and the
probabilities available on its blocks. It allows zero masses, as in the
manuscript. The fourth colour has probability `span i j`. For distinct atoms
`i,j`, their unique pairing colour has off-diagonal probability `pair i j`
and diagonal probabilities `diag i j` and `diag j i`. The three pairings are
`{01,23}`, `{02,13}`, and `{03,12}`. Thus the constraints say:

- off the diagonal, `span i j + pair i j = 1`;
- on atom `i`, `span i i + sum (diag i j, j != i) = 1`.

All probabilities that enter an energy lie in `[0,1)`. `spanEnergy` is the
ordered double sum for the spanning colour. `pairEnergy i j` is the entropy
of the paired component `{i,j}`, including both diagonal contributions and
both off-diagonal terms. `pairEnergy_symm` proves that reversing `i,j` gives
the same energy, so there are six paired energies and one spanning energy.
These energies are the **squared** energies used by the general program's
square-root objective.

## Checked results

- `Patterns.lean`: `lemma2` classifies every four-coordinate word family of
  Hamming diameter at most two. `PatternFamily` explicitly states the three
  alternatives: two fixed coordinates, a radius-one ball with arbitrary
  centre, or the four-word triangle after coordinate and symbol relabelling.
  The proof works for any nonempty alphabet with decidable equality, and
  includes empty families. Three suitable words constrain any compatible
  word to a ball plus one exception; the exception forces the triangle.
- `ProgramPatterns.lean`: `component_words_close` derives Hamming diameter
  at most two directly from program feasibility. The theorem
  `component_pattern_classification` applies Lemma 2 to actual component
  instances; distinctness of their label words is unnecessary.
- `Parameters.lean`: existence and uniqueness of `p` in `(0,1)` satisfying
  `3*p^6 + 2*p - 2 = 0`. `parameter` names this root.
- `Analytic.lean`: logarithmic tangent bounds, the two-colour weighted-cost
  inequality, explicit lower bounds for `log(3/2)` and `log 2`, and
  `tStar p = -(3/4)*log p < 2213/10000` for the positive polynomial root.
- `LargeAtom.lean`: `lemma3` proves that every atom has mass strictly below
  `2/5` if all seven energies are at most `tStar p`. The specialization
  `lemma3_at_optimum` uses the uniquely defined `parameter`, with no extra
  analytic estimates as hypotheses. The stronger
  `PairingData.large_atom_of_threshold` proves the conclusion even if all
  seven energies are merely bounded by `2213/10000`.
- `Entropy.lean`: defines `entropy = H`, its derivative `entropySlope`,
  `weight = (1-parameter)/parameter`, and the manuscript's coefficients.
  It proves the derivative identities and `1/3 < weight < 11/32`.
- `Coefficients.lean`: the strict inequalities `alphaCoefficient > 5/4`
  and `gammaCoefficient > -1`, using rational logarithm estimates directly.
- `EntropyQuadratic.lean`: the bound
  `entropy (w+d) >= entropy w + entropySlope w*d - 2*d^2` whenever
  `w >= 1/3` and `abs d <= 3/20`. A polynomial correction makes the entropy
  remainder convex on this interval, so Mathlib's stationary-point minimum
  theorem supplies the bound. This replaces the manuscript's integral
  Taylor-remainder calculation and proves the estimate uniformly for all
  `w >= 1/3`.
- `Lemma4.lean`: `lemma4` combines every inequality of Lemma 4, with the
  manuscript's uniquely defined algebraic parameter and no extra hypotheses.

## Reused public code and verification

The Hamming metric comes from Mathlib's
[`InformationTheory.Hamming`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/InformationTheory/Hamming.lean).
The numerical logarithm estimates use the already-proved partial-sum bounds
`Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add` in
[`Log.Deriv`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean).
The tangent estimates use `Real.log_le_sub_one_of_pos`. No separate graphon
or minor theory is needed for these lemmas. The quadratic entropy bound
reuses `convexOn_of_hasDerivWithinAt2_nonneg` and
`ConvexOn.isMinOn_of_rightDeriv_eq_zero` from Mathlib's
[`Convex.Deriv`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Convex/Deriv.lean).

Run `lake build` and `python3 scripts/check_proofs.py` at the repository root.
The default build includes this development; its root module prints the
kernel dependencies of the public results.
