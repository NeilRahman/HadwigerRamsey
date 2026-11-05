# Component optimization proof guide

The main four-colour Hadwiger–Ramsey asymptotic and its exact leading
constant are stated in the [README](README.md). This guide records the
supporting optimization results and their implementation.

This development formalizes **Theorem 1, Lemmas 2–4, Proposition 5, and Lemma 6** of the local manuscript
`four_colour_analytic.tex`. It builds on the general component program in
`ComponentTransfer`. The manuscript is excluded from version control.

## Exact optimum and attainment

`Theorem1.lean` proves the full finite-program optimum. For every `p` with
`0 < p < 1` and `3*p^6 + 2*p - 2 = 0`, its public theorem is:

```lean
theorem theorem1 {p : ℝ} (hp : 0<p ∧ p<1 ∧ 3*p^6+2*p-2=0) :
    beta4^2=-(3/4 : ℝ)*Real.log p ∧ attainingInstance.objective=beta4
```

`AttainingConstruction.lean` specifies `attainingInstance` explicitly:
four masses `1/4`; partitions `{01,23}`, `{02,13}`, `{03,12}`, and
`{0123}`; diagonal densities `(1/3,1/3,1/3,0)`; and off-diagonal densities
`parameter` in the unique pairing colour and `1-parameter` in the spanning
colour. Its feasibility and all component entropies are checked directly.
The unique root is named `parameter`; `beta4_eq` also gives the square-root
form of the optimum.

The lower bound applies to every original `ComponentInstance 4` via
`instance_lower_bound`, with no assumption on its number of atoms or
component pattern. `FiniteProgram.lower_bound` is the corresponding result
for arbitrary finite atom and label types.

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
- `StabilityData.lean`: the weights `pairWeight = w_ij`, row sums
  `rowWeight = S_i`, logarithmic terms `diagonalDual = D_i`, and
  `dualValue = N(a)`. It proves the exact row and variance identities.
- `StabilityMoments.lean`: bounds on the second through fourth moments,
  including `sum a_i^2 <= 9/25`, and the final stability polynomial bound.
  The square-sum cap uses a finite pair-merging argument and algebraic
  inequalities; Cauchy–Schwarz supplies the centered fourth-moment bound.
- `StabilityIdentities.lean`: the exact moment expansions and the baseline
  identity `uniformValue = (1+6*weight)*tStar parameter`.
- `StabilityEntropy.lean`: diagonal logarithm and off-diagonal entropy
  estimates, combined into `four_atom_stability` with the manuscript's
  exact coefficient `3/100`.
- `WeightedCosts.lean` and `PairingDual.lean`: the general weighted
  two-colour inequality, diagonal tangents at possibly negative formal
  densities, and the weighted dual bound relating `N(a)` to actual feasible
  component energies. The theorem `PairingData.optimum_lower_bound` proves
  that any common upper bound on the seven component energies is at least
  `tStar parameter`, without an atom-size assumption.
- `Lemma5.lean`: `lemma5` is the stability assertion of Proposition 5;
  `lemma5_pairing_lower_bound` is its concluding assertion for feasible
  pairing patterns. `dualValue_eq_unordered` verifies that the code's
  ordered off-diagonal sum equals the manuscript's `2 * sum (i < j)`.
- `CapacityNumerics.lean`: exact rational enclosures of the exponential at
  `251/200` and `41/40`, and the logarithmic estimate at the second anchor.
  These use Mathlib's checked exponential Taylor bounds and logarithm series.
- `CapacityCalculus.lean`: a reusable anchor argument for square-root
  normalization. The normalized function increases before the anchor;
  after the anchor, its derivative bound controls the barrier `C * sqrt z`.
  This avoids constructing a global maximizing critical point.
- `CapacityFirst.lean`: `1 - exp(-z) <= (16/25) * sqrt z` for `z > 0`.
  Convexity of the exponential supplies the head estimate at `251/200`.
- `CapacityLog.lean` and `CapacitySecond.lean`: the derivative identities,
  concavity of the logarithmic derivative test on `[0,41/40]`, and
  `3 * log((3-exp(-z))/2) <= (413/500) * sqrt z` for `z > 0`.
- `Capacity.lean` and `Lemma6.lean`: `capacityF` and `capacityG` with the
  manuscript's zero-mass convention, the exact substitution `z = t/s^2`,
  and `lemma6`, proving both capacity bounds for every `t > 0` and `s >= 0`.

## Completing the classification argument

- `FiniteProgram.lean` expresses the same program with arbitrary finite
  atom and label types and a common entropy bound.
- `BlockAverages.lean`, `Merging.lean`, and `MergingEntropy.lean` merge equal
  full component-label words. Mathlib's finite Jensen inequality for the
  concave logarithm proves that no component entropy increases; the merged
  words are distinct.
- `ComponentCapacity.lean` derives component density capacities by the same
  logarithmic Jensen bound, and proves monotonicity in component mass.
- `ThresholdBounds.lean` proves the strict numerical estimates at
  `2213/10000` with rational exponential and logarithm bounds.
  `FixedPattern.lean` excludes the two-fixed-coordinate case.
- `BallGeometry.lean`, `BallEntropyBasic.lean`, `BallAggregation.lean`,
  `BallNumerics.lean`, and `BallExclusion.lean` exclude a radius-one ball.
  The class masses include the possible centre and the four arms. The
  entropy estimate forces an arm of mass greater than `33/50`; its main
  component then has mass below `17/50`, contradicting the density capacity
  bounds. Individual singleton components are kept separate throughout.
- `ReindexProgram.lean`, `PairingReduction.lean`, and `TriangleReduction.lean`
  connect the surviving pattern to `PairingData`. A missing triangle word
  puts the other three words in a radius-one ball, so all four words must
  occur below the threshold. This avoids extending the densities to absent
  atoms. The finite relabelling preserves all constraints and entropies.
- `Theorem1.lean` applies the classification, proves the lower bound for the
  original program, and combines it with the attaining construction.

## Reused public code and verification

The merging and component-capacity steps reuse `ConcaveOn.le_map_sum`
from Mathlib's `Analysis.Convex.Jensen`, applied to `Real.strictConcaveOn_log_Ioi`.
Finite sums are regrouped using `Finset.sum_fiberwise`.
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
The moment estimates reuse `Finset.sum_mul_sq_le_sq_mul_sq` from Mathlib's
[`BigOperators.Ring.Finset`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean).
The capacity estimates reuse Mathlib's `Real.sum_le_exp_of_nonneg`,
`Real.exp_bound'`, convexity of `exp`, and derivative monotonicity and
concavity theorems. All transcendental numerical bounds are proved from
these results with exact rational arithmetic.

Run `lake build` and `python3 scripts/check_proofs.py` at the repository root.
The default build includes this development; its root module prints the
kernel dependencies of the public results.
