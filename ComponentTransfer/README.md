# Proposition 4.1: component transfer

This directory proves **Proposition 4.1**: for every fixed number of
colours `r ≥ 2`, `ComponentTransfer.theorem5` proves the unconditional limit
`hadwigerRamsey r k / (k * sqrt(log k)) → (beta r)⁻¹`.

The Lean development roughly follows the arguments in
[comptransfer.tex](comptransfer.tex), whose Theorem 5 is Proposition 4.1.
Theorems 3 and 4 and Lemmas 6–8 of that companion source supply the supporting
results. Their numbers below refer to the companion source, not to the main
paper. The implementation details are described below.

Proposition 4.1 is used by [Proposition 4.2](../HadwigerRamsey4Col/README.md)
to obtain the four-colour asymptotic from the exact component optimum.

The optimization parameter is defined from the manuscript's finite component
instances, independently of the Ramsey number.

## Implemented results

- `Construction.lean`: `ComponentTransfer.theorem4` proves that for every
  `r ≥ 2` and `ε > 0`, all sufficiently large integer orders `n` have an
  `r`-edge-colouring of the complete graph in which every colour graph has
  Hadwiger number at most `(beta r + ε) * n / sqrt (log n)`.
  `constructionBound` is the equivalent filter formulation. The proof uses
  the previously checked random-minor bound (Theorem 1 of this manuscript).
- `ConstructionParameters.lean`: a common positive error parameter for the
  finite family of component estimates, the probability union bound, and
  the strict margin above the near-minimizing objective.
- `ConstructionPartition.lean`: canonical component enumeration and exact
  class-mass identities under restriction.
- `ConstructionFinite.lean`: the complete finite random-colouring argument,
  including one outcome satisfying all component estimates and avoiding
  every zero-probability edge event.
- `ConstructionAsymptotic.lean`: each positive-energy component eventually
  satisfies the random-minor hypotheses and its estimate fits within the
  desired bound expressed in terms of the total graph order.

- `ComponentProgram.lean`: positive masses summing to one; arbitrary colour
  partitions encoded by label maps; symmetric densities in `[0,1)` summing
  to one and vanishing between different parts; component energies and their
  maximum; the infimum `beta r`; the bound `1/r ≤ beta r`, positivity, and
  near-minimizing instances. Unused labels are empty parts with zero energy.
- `Ramsey.lean`: general complete-graph edge colourings, the least order
  forcing a monochromatic clique minor, and asymptotic inversion of positive
  matching transfer and construction bounds. This reuses the project's
  branch-set minor definition and previously checked rounding/scale results.
- `Asymptotic.lean`: `ComponentTransfer.theorem5` proves the exact ratio-limit
  conclusion of Theorem 5 by applying the asymptotic inversion theorem to
  the proved transfer and construction bounds. The reusable conditional
  deduction `theorem5_of_theorems3_and4` is also retained.
- `Sampling.lean`: independent categorical edge colours with prescribed
  probabilities, a finite union bound also avoiding null events, and the
  bound on a graph's Hadwiger number from its separate component bounds.
- `ConstructionRounding.lean`: partitions for every integer order whose
  relative part sizes converge to arbitrary prescribed positive masses.
- `ConstructionLimits.lean`: component order, entropy, and logarithmic
  normalization limits used in the random construction.
- `TransferCore.lean`: `ComponentTransfer.lemma6` has Lemma 6's exact
  sufficiently-large-order quantifiers, including the strict retained-size
  bound and connectivity at least `floor (sigma * n / 2)`. The stronger
  `connected_core` proves this for every `n ≥ 2`. The proof uses an extremal
  retained vertex set and charges cut edges to deleted separators.


- `RealizationLemma.lean`: `ComponentTransfer.lemma7` realizes every finite
  measurable partition into positive-measure sets along any graph sequence
  whose orders tend to infinity and which converges in the common coloured
  cut metric. `RealizesPartition` spells out all three conclusions: relative
  part sizes, ordinary block edge densities (including the diagonal
  `e / choose(size, 2)` convention), and induced convergence on every nonempty
  union, with normalized restricted measure. Empty unions have no normalized
  probability restriction. The vertex label maps are defined at every index;
  their fibres are nonempty eventually, as follows from the positive limits.
  The theorem works on arbitrary probability spaces, including the unit
  interval, and permits empty graphs at finitely many initial indices.
- `RealizationProbability*`, `RealizationCombinatorics`, and
  `RealizationCouplingInput`: independent conditional sampling from actual
  common probability couplings, collision and variance bounds, and one
  deterministic choice realizing a countable family of marked coloured
  graph tests. Convergence means one coupling controls every colour, rather
  than a separate alignment for each colour.
- `RealizationCounting`, `RealizationWeightedCounting`,
  `RealizationCommonApproximation`, and `RealizationTransportMeasure`:
  coloured counting with measurable vertex constraints, finite step
  approximations shared by all colours, and actual couplings matching their
  cell masses. These reuse the public graphon foundations documented in
  `../vendor/graphon/README.md`.
- `RealizationC4Pattern`, `RealizationConvergence*`, `RealizationInduced`,
  and `RealizationRestriction`: the signed four-cycle bound that recovers
  common cut convergence from the realized tests, exact induced-subgraph
  normalization, and graphon restriction using conditional probability.

- `LiftingLemma.lean`: `ComponentTransfer.lemma8` proves the entropy lower
  bound for any finite family of disjoint positive-measure subsets of a
  connected positive-measure graphon restriction. Its extended nonnegative
  entropy uses exactly `-log 0 = +∞`, so density-one entries give the infinite
  conclusion. The theorem needs only graph orders tending to infinity.
- `LiftingExpansion*` and `LiftingCutTransfer`: connected graphons have a
  uniform positive bound on balanced fractional cuts. The proof represents
  these cuts in a weak dual compact set, uses finite step approximations for
  continuity, and transfers the bound through actual probability couplings
  using Radon–Nikodym derivatives. This supplies the connected-limit cut
  expansion used by Lemma 8.
- `LiftingRealization`, `LiftingPositivePartition`, `LiftingRegion`, and
  `LiftingPartitionData`: realize a prescribed region and extend the selected
  sets to a positive partition, including null remainder or complement sets.
- `LiftingFinite`, `LiftingStability`, `LiftingDeletion`, `LiftingAsymptotic`,
  and `LiftingEntropy`: apply the existing density-sensitive minor theorem
  to the connected cores from Lemma 6, control deletion errors and density
  caps, and pass to the exact extended entropy lower limit.

- `Transfer.lean`: `ComponentTransfer.theorem3` proves the exact eventual
  lower bound for every complete graph edge colouring; `transferBound` is
  its filter formulation. A counterexample sequence would have a fixed
  normalized minor bound strictly below `beta r`.
- `TransferRegularity`, `TransferCompactness*`, and
  `TransferFinitePresentation`: common finite partitions and finite nets
  for coloured graphons, one shared sequence of alignments, scalar limit
  extraction, and preservation of the colour sum in the limit. This proves
  the common coloured compactness used in the transfer argument.
- `TransferInvariant`, `TransferProfile`, `TransferConnected`, and
  `TransferComponentLabels`: countable connected-component decomposition
  from a dense family of invariant measurable cuts. The natural-number
  labels distinguish positive connected parts from the zero-degree remainder.
- `TransferAtoms` and `TransferGraphon`: the common countable refinement,
  exact masses and averaged densities, and Lemma 8 applied to each finite
  same-component family. The zero-degree remainder has zero entropy.
- `TransferOptimization*` and `TransferConclusion`: finite entropy bounds
  exclude density one; truncating and normalizing finitely many atoms
  gives a component instance. Its objective contradicts the counterexample
  bound, completing Theorem 3.

## Local checks

Run `python3 scripts/check_proofs.py` and `lake build` from the repository root.
The default Lake build includes these modules and prints their theorem
dependencies. The unconditional endpoint reports include `theorem3`, `theorem4`, and
`theorem5`, as well as the supporting lemmas.
