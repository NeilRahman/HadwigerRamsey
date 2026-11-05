# Vendored graphon foundations

These files are from Cameron Freer's [graphon library](https://github.com/cameronfreer/graphon),
commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e` (Apache 2.0; see `LICENSE`).
The upstream project pins Lean/Mathlib 4.32.0. This subset has been compiled
against this repository's pinned Lean/Mathlib 4.33.0.

The subset contains the dependency closure of `Graphon.Counting`: `Basic`, `Step`,
`CutNorm`, `HomDensity`, `Pullback`, `MeasureIso`, `CutDistance`, and `Counting`.
It also includes `Approximation`, `Regularity`, `FiniteFactorApproximation`,
`CutNormPullback`, `Overlay`, and `Compactness` for finite marked
approximations, coupling estimates, and scalar graphon compactness.
It supplies symmetric measurable graphons, finite-graph step graphons,
cut norms and cut distances, measure-preserving pullbacks and alignments,
homomorphism-density counting bounds, the Frieze--Kannan regularity lemma,
cut-norm contraction under maps between different probability spaces, the
measure-preserving equivalence overlay theorem, and scalar graphon compactness.

Local modifications:

- Removed the `Architect` imports and the blueprint title attributes. These
  supply documentation metadata and are not used in the proofs.
- Exposed `Graphon.counting_integrable_term` and
  `Graphon.weighted_prod_graphon_diff_le` by removing `private`, so first-party
  coloured counting lemmas can reuse the already-proved measure-theoretic
  endpoint-conditioning argument.

- Exposed `Graphon.exists_cutNormDiff_limit_of_summable` by removing `private`.
  Common coloured compactness applies this scalar limit construction to each
  colour after constructing one shared sequence of alignments.
- In one documentation comment in `Compactness`, replaced the phrase
  `axiom-clean` with `dependency-clean` so the repository's source guard does
  not mistake that comment for a declaration.

The original twelve files were compared against the pinned upstream source
with their documented metadata and visibility changes. `Overlay` and
`Compactness` underwent the same metadata removal, plus the visibility and
comment changes listed above. No mathematical statement or proof was changed.
The upstream `NeZero n` assumptions on some adjacency helper lemmas are
preserved; the first-party realization code proves the corresponding elementary
facts for empty carriers where needed.

Every `Graphon` import in this subset resolves to another file in this subset;
all remaining imports come from Mathlib. The source guard checks the vendored
files as well as first-party code, and the downstream theorem dependency
reports check the imported proof chain.
