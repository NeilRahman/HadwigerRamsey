# Formalization status

Theorem 1.5 (`thomasonupper`) from the October 31 manuscript is **proved
in Lean 4.33.0** as `HadwigerRamsey.thomasonupper` in
`HadwigerRamsey/ThomasonUpper.lean`. The exact statement and all logical
differences from the manuscript argument are recorded in its section below.

Theorem 1.4 (`thomasonlower`) of `hadramoct30.tex` is proved in Lean 4.
The endpoint is `HadwigerRamsey.thomasonlower` in
`HadwigerRamsey/ThomasonLower.lean`.

Lemma 3.1 (`bigset`) is also proved, for a nonempty ground set, as
`HadwigerRamsey.bigset` in `HadwigerRamsey/BigSet.lean`.

## Exact meaning of the endpoint

For each positive real ε, the theorem supplies a natural cutoff n₀ before
quantifying over n, the number of classes k, the partition, the symmetric
probability matrix, or the probability space. Thus the cutoff is uniform
in all of those data, as required in the manuscript.

Vertices are `Fin n`. A class map `τ : Fin n → Fin k` represents the
partition. `classMass τ i` is the cardinality of its fiber divided by n;
`blockLambda τ p` is precisely the manuscript's double sum of
`αᵢ αⱼ (-log (1-pᵢⱼ))`. Its square root is L. Empty classes are allowed,
which only strengthens the result and leaves their contribution zero.

The random graph is `G : Ω → SimpleGraph (Fin n)` on any probability
space. The assumptions require measurable, mutually independent
undirected edge events, with probabilities `p (τ u) (τ v)`. Independence
is Mathlib's `ProbabilityTheory.iIndepSet`, not a substitute definition or
an assumed bound on partitions. It is enough to specify increasing pairs
of vertices because graphs are undirected. This formulation applies to
the independent-edge random graph of the manuscript without committing
to one particular construction of its sample space.

`HasCliqueMinor G s` uses pairwise disjoint connected branch sets and an
edge between every distinct pair. Connectedness is Mathlib's induced-graph
`SimpleGraph.Connected`, including nonemptiness. `hadwigerNumber` is the
maximum possible minor order. The graph module proves that the maximum
is attained and that having a clique minor of order s is equivalent to
`s ≤ hadwigerNumber G`. No connection to an alternative graph-minor API
is needed for this branch-set definition.

The conclusion is the manuscript's real-valued probability inequality:
the probability of `hadwigerNumber G ≤ (1+ε) L n / sqrt(log n)` is at
least `1-ε`. Logarithms are natural. The case ε ≥ 1 is covered directly
by nonnegativity of probability.

## Paper-to-Lean map

| Manuscript ingredient | Lean declaration / module |
| --- | --- |
| Minor gives permissible partition (`obs:minor-partition`) | `HasCliqueMinor.permissible`, `Graph.lean` |
| Hadwiger number and branch-set meaning | `hadwigerNumber`, `hasCliqueMinor_iff_le_hadwigerNumber`, `Graph.lean` |
| Total-weight identity (`lem:total-weight`) | `total_weight_identity`, `Weights.lean` |
| Disjoint block pairs use independent edges | `probability_allHits`, `Probability.lean` |
| Probability of no edge across a block pair | `probability_noHit`, `Probability.lean` |
| Finite Jensen and exponential product estimate | `sum_exp_neg_ge`, `permissible_product_bound`, `Analytic.lean` |
| Fixed-partition bound (`lem:fixed-partition`) | `fixed_partition_bound`, `Finite.lean` |
| Union bound (`cor:finite`) | `finite_minor_bound`, `Finite.lean` |
| Uniform asymptotics (`lem:uniform-decay`) | `uniform_tail_bound`, `Asymptotic.lean` |
| Block average equals vertex-pair average | `blockLambda_identity`, `Blocks.lean` |
| Measurability of finite graph properties | `measurableSet_graph_property`, `Measurability.lean` |
| Theorem 1.4 (`thomasonlower`) | `thomasonlower`, `ThomasonLower.lean` |
| Lemma 3.1 (`bigset`), nonempty ground set | `bigset`, `BigSet.lean` |

The finite probability result is slightly more general: logarithmic
weights may vary independently on every potential edge. The final
wrapper specializes it to the block probabilities and the exact L in
the manuscript. The rounding argument uses `ceil R`; excluding a minor
of that order gives `hadwigerNumber < R`, which implies the stated weak
inequality, including when R is an integer.

## Verification

Pinned Lean: `leanprover/lean4:v4.33.0`.
Pinned Mathlib: tag `v4.33.0`, commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.
All transitive dependencies are recorded in `lake-manifest.json`.

Run:

```sh
source "$HOME/.elan/env"
lake exe cache get
python3 scripts/check_proofs.py
lake build
```

The root module prints the endpoint's kernel axiom dependencies. The
expected list is exactly `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders or project-defined axioms. GitHub Actions
repeats the build and source guard on pushes and pull requests.

The original manuscript stays local and is preserved without edits. It and
local counterexample notes are excluded from version control. The mathematical correspondence above is documented for
human review; kernel checking establishes the Lean statement.

## Lemma 3.1: two partitions (`bigset`)

The endpoint `HadwigerRamsey.bigset` uses Mathlib's existing
`Finpartition s` directly, for a finite set `s`. It assumes `s.Nonempty`,
that each partition has at most k parts, and ε > 0. It proves exactly the
stated alternatives: a part of either partition has size at least
(1−ε)|s|, or there are A and B of size at least ε|s|/k² lying in distinct
parts of both partitions. The subsets are chosen as intersections of
parts; no new partition notion is introduced.

**Boundary condition:** the manuscript does not explicitly require n > 0.
With the usual definition of partitions into nonempty parts, its literal
statement fails for n = 0: both partitions are empty, so neither outcome
can supply the required parts. The Lean theorem makes the nonemptiness
condition explicit. It implies k > 0 from the partition-size bound, so
no separate positivity assumption on k is needed. This is the version
used by the later application to a large vertex set. The manuscript has
not been edited.

The proof follows the manuscript. Large intersection cells cannot differ
in both their row and column if the second outcome fails. A short logical
helper, `supported_on_row_or_column`, shows that all such cells then lie
in one row or one column, also handling the case of no large cells.
`large_part_of_small_other_intersections` bounds the total size outside
that row/column. It reuses Mathlib's partition disjointness and coverage,
`Finpartition.sum_card_parts`, `Finset.card_biUnion`, and finite sum/cardinality
inequalities. `sum_card_inter_parts` packages the intersection-counting
identity needed by this argument.

A targeted public search and a search of the pinned Mathlib sources found
finite-partition and pigeonhole infrastructure, rather than an existing
copy of this exact lemma. The reusable partition API is
[Mathlib.Order.Partition.Finpartition](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Order/Partition/Finpartition.lean)
(by Yaël Dillies and Bhavik Mehta). Mathlib's weighted pigeonhole results
were also inspected; direct finite sums suffice here. `BigSet.lean` is new
project code; the underlying finite-partition implementation is reused
without modification.

Both endpoints have an axiom report in the root module and are included
in the same build and source guard.

## Related formalizations and reused results

Search performed on 31 October 2026. Targeted searches for the paper's
title, authors, random clique minors, and permissible partitions did not
locate a complete existing formalization of the Bollobás–Catlin–Erdős
result. This is a search outcome, not a claim that none exists.

- [Bollobás, Catlin, and Erdős (1980), original paper](https://users.renyi.hu/~p_erdos/1980-10.pdf):
  the homogeneous permissible-partition upper-bound argument is on pages
  196–197; the fixed-p extension is stated on page 198. This is the
  mathematical source, not a Lean dependency.
- [uw-math-ai/random_graphs](https://github.com/uw-math-ai/random_graphs):
  an Erdős–Rényi random-graph formalization project. Its README also links
  earlier work by Yael Dillies. It was located as related infrastructure;
  no source from it is vendored or assumed here.
- [snorin239/LinearHadwiger](https://github.com/snorin239/LinearHadwiger):
  a related Lean formalization about coloring and clique minors. Its main
  result is different from this random-graph upper bound. It is not a
  dependency of this project.
- [Mathlib finite Jensen](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Convex/Jensen.lean):
  `convexOn_exp.map_sum_le` is reused directly.
- [Mathlib independence](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Probability/Independence/Basic.lean):
  the proof reuses `iIndepSet_iff` and
  `iIndepSet.indep_generateFrom_of_disjoint`, along with measurable
  generated events and the measure-of-intersection product identity.
- [Mathlib power/logarithm asymptotics](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean):
  `isLittleO_log_rpow_rpow_atTop` supplies the growth estimates.
- Mathlib also provides finite union bounds, exponential/logarithm and
  square-root identities, ceilings, finite sums, and graph connectivity.

The earlier two formalizations use Mathlib directly. Lemma 3.6 additionally
uses the vendored LeanCert interval-analysis subset described below.


## Lemma 3.6: optimization (`fopt`)

The endpoint is `HadwigerRamsey.fopt` in `HadwigerRamsey/FOpt.lean`.
It quantifies over every natural k and α : Fin k → ℝ, assumes αᵢ ≥ 0
and ∑αᵢ = 1, and proves ∑f(αᵢ) ≤ log 2 − β² with exactly the
manuscript's β = sqrt(−log(10−4 sqrt 6))/2. The public definitions are
`HadwigerRamsey.beta` and `HadwigerRamsey.optimizationFunction`.

### Complete differences from the manuscript's argument

1. **Endpoint completion:** the manuscript defines f only on [0,1),
   although its hypotheses allow αᵢ = 1 and its proof uses h(1). We use
   the same formula at x = 1. At x = 0 the total Lean expression equals
   zero and agrees with the specified f(0). No extra hypothesis excludes
   zero weights or a weight of one. Values outside [0,1] are irrelevant.
2. **Exact constants:** write q = 10 − 4 sqrt 6, c = −log(q)/4 = β²,
   F = log 2 − c, and a = 4F − 16cq/(2−q). The auxiliary constant a
   and cubic P(x) = Fx + ax(x−1/2)(1−x) are new. Lean proves a ≥ 0.
   The identity (2−q)² = 16q proves 2f(1/2) = F exactly, retaining
   that part of the manuscript. The choice of a also makes P and f
   have equal first derivatives at 1/2.
3. **A stronger pointwise bound replaces the reduction to two weights:**
   prove f(x) ≤ P(x) for every x ∈ [0,1]. We do not establish or assume
   monotonicity of f(x)/x on (0,1/2]. We never divide by a weight or by
   1−α₁, so the zero-weight and α₁ = 1 cases need no exception.
4. **Whole-interval bounds replace the plotted root/sign argument:**
   for D = P−f, prove D ≥ 0 on [0,0.35] analytically from
   f(x) ≤ x² log 2 and rational coefficient bounds. On [0.35,0.4]
   and [0.6,1], exact rational interval certificates prove D ≥ 0
   on cells of width 1/1000. On [0.4,0.6], certificates prove
   D″ ≥ 0; Mathlib's calculus and convexity results, together with
   D(1/2) = D′(1/2) = 0, give D ≥ 0. The outer certificates use
   indices 350–399 and 600–1000; curvature uses 400–600, so boundaries
   are covered with overlap. The slight extra coverage beyond the
   desired intervals is harmless. There is no assertion about the
   number or location of roots of h′, no approximate critical point,
   and no use of the comparison h(1) ≈ 0.284 < F ≈ 0.293.
5. **The final summation is algebraic:**
   P(x+y)−P(x)−P(y) = 3axy(1−x−y) ≥ 0 for x,y ≥ 0, x+y ≤ 1.
   Induction yields ∑f(αᵢ) ≤ ∑P(αᵢ) ≤ P(∑αᵢ) = P(1) = F.
   This handles all finite k directly, instead of choosing a largest
   weight and studying h(x) = f(x)+f(1−x).
6. **Numerical evidence is replaced by proved error bounds:**
   the rational boxes are
   q ∈ [202041028,202041030]/10⁹,
   c ∈ [399821,399822]/10⁶,
   F ∈ [293325,293327]/10⁶,
   a ∈ [4544,4545]/10⁴, and
   log 2 ∈ [693147,693148]/10⁶.
   The q bounds follow from (sqrt 6)² = 6. The others follow from
   proved logarithm interval bounds. Each exponential/logarithm
   interval is rounded outward to multiples of 10⁻⁹, with a proof
   that containment is preserved. Certificate depth is 16; the
   constant bounds use depth 20. `decide +kernel` checks each finite
   cell through ordinary kernel reduction. Floating-point experiments
   helped choose the envelope, but are absent from the proof premises.

The hypotheses and conclusion are unchanged apart from completing f(1).
The manuscript itself is unedited. The root-count and monotonicity claims
from its particular argument are neither required nor verified by this
alternative proof.

### Reuse and module map

The pinned Mathlib supplies real differentiation rules, logarithm and
square-root identities, finite sums, and
`convexOn_of_hasDerivWithinAt2_nonneg` together with
`ConvexOn.isMinOn_of_rightDeriv_eq_zero`. The public
[LeanCert project](https://github.com/alerad/leancert/tree/122a3776fe157f92ee8a1116faf079378bcf18af)
supplies the rational interval and Taylor/logarithm enclosure theorems.
The exact source, notices and compatibility changes are recorded in
`vendor/lean-cert/README.md`. This is reused analytic infrastructure,
not an existing formalization of this particular optimization inequality.
A targeted public search for the Hadwiger–Ramsey optimization lemma did
not locate a pre-existing proof of the exact inequality.

The new first-party modules are:

- `FOpt/Definitions.lean`: constants and exact half-point identities.
- `FOpt/Algebra.lean`: cubic superadditivity and the finite-sum argument.
- `FOpt/Calculus.lean`: both derivatives and tangency at 1/2.
- `FOpt/Interval.lean`: sound expression bounds and outward rounding.
- `FOpt/Constants.lean`: certified boxes for the constants.
- `FOpt/Certificates.lean`: finite whole-cell checks in blocks of ten.
- `FOpt/Coverage.lean`: coverage of the required intervals by these blocks.
- `FOpt/Envelope.lean`: analytic small interval, convex middle interval,
  outer interval coverage and the global cubic bound.
- `FOpt.lean`: manuscript-facing definitions and theorem.

The three endpoints above are imported and their dependency reports
printed in `HadwigerRamsey.lean`. The source guard also checks vendored
Lean sources. The fopt endpoint requires only `propext`,
`Classical.choice`, and `Quot.sound`.


## Optimization lemma (`opt`)

`HadwigerRamsey.opt` in `HadwigerRamsey/Opt.lean` proves the manuscript's
three-way alternative with positive weights summing to one, probabilities
in [0,1), the exact diagonal/off-diagonal sum conditions, and the same β.
The conclusion writes out the manuscript's negative double sums explicitly.
Matrix symmetry is not required, consistently with the statement of `opt`.
No additional hypotheses or numerical approximations are introduced.

The argument follows the manuscript: negate the alternatives, square the
three strict inequalities, average the two matrix costs, use logarithm
concavity, bound the diagonal terms by f(αᵢ), and contradict `fopt`.
Mathlib's `Real.strictConcaveOn_log_Ioi.concaveOn` directly supplies the
midpoint inequality, which is equivalent to convexity of −log(1−x).
The other reused results include `Real.log_le_log`,
`Real.le_log_iff_exp_le`, `Real.log_div`, `Real.sq_sqrt`, `Real.sqrt_lt`,
and finite-sum distribution and comparison theorems. There is no new
analytic library or vendored code for this lemma.

### Mathematical correspondence and differences

- The averaging step uses the **sum** of the two logarithms, implementing
  the agreed correction to the two minus signs in the manuscript.
  All sums use the same index set `Fin k`, implementing the agreed fixes
  of the stray k/ℓ indices (the Lean name k simply denotes the dimension).
- `Optimization.logCost p` abbreviates −log(1−p).
  `Optimization.energy α q` is the sum of the weighted logarithmic costs;
  `energy_eq_neg_sum` proves equality with the displayed negative double
  sum. The identity −log((1+pᵢ)/2) = log 2 − log(1+pᵢ) packages the
  manuscript's diagonal/off-diagonal algebra as the reusable bound
  `energy_average_lower`.
- The stronger helper `Optimization.opt_of_nonneg` permits αᵢ = 0 and
  replaces the exact mass equalities by pᵢ+qᴮᵢᵢ+qᴳᵢᵢ ≥ 1 and
  qᴮᵢⱼ+qᴳᵢⱼ ≥ 1 for i ≠ j. This is proved directly, using monotonicity
  of the logarithmic cost before the same midpoint inequality. It does
  not require rescaling probabilities. The public `opt` theorem
  specializes the helper to the original positive-weight/equality
  hypotheses. The stronger helper is available for reuse; the later `optapprox` proof
  instead uses the explicitly requested reduction to the public `opt` theorem.
- In `diagonal_le_function`, a zero weight is handled directly before
  division by αᵢ². For a positive weight, the proof follows the
  manuscript's exponential comparison. The constant β is proved
  positive as `HadwigerRamsey.beta_pos`, and all logarithm domains and
  radicand nonnegativity are justified explicitly. These are consequences
  of the existing assumptions, not new conditions.
- There are no other logical changes to the `opt` argument. The
  `optapprox` corollary is treated separately below.

The manuscript source remains unchanged; the preceding corrections are
implemented in the Lean proof and recorded here. The `optapprox`
formalization below uses the agreed closed bounds and explicitly positive δ.

The root module imports `Opt.lean` and prints dependency reports for both
`opt` and `Optimization.opt_of_nonneg`. Both use only `propext`,
`Classical.choice`, and `Quot.sound`, including their dependency on `fopt`.


## Approximate optimization corollary (`optapprox`)

`HadwigerRamsey.optapprox` in `HadwigerRamsey/OptApprox.lean` proves the
agreed closed version of the corollary: for every ζ > 0 there is δ > 0,
uniform in every positive dimension k ≤ 1/ζ and every choice of data.
Weights satisfy αᵢ ≥ 0 and ∑αᵢ = 1; probabilities satisfy
0 ≤ pᵢ,qᴮᵢⱼ,qᴳᵢⱼ ≤ 1−ζ. Matrix symmetry is included as in the manuscript.
The conclusion is that conditions (a)–(e), with exactly their stated weak
inequalities, cannot all hold. The negative double sums are written out
explicitly in the public statement, with the same β as before.
There is no additional restriction such as ζ < 1 or αᵢ > 0.

### Explicit dependency on `opt`

The new proof does not directly invoke `Optimization.opt_of_nonneg`.
Instead its checked proof dependencies follow this chain:

`optapprox` → `OptApprox.bounded_dimensions` →
`OptApprox.fixed_dimension` → `OptApprox.defect_pos_on_bad` →
`Optimization.opt_closed_from_opt` →
`Optimization.opt_nonneg_equalities_from_opt` →
`Optimization.opt_fintype` → **`HadwigerRamsey.opt`**.

`OptApprox/DependencyAudit.lean` inspects the elaborated proof expressions,
checks that this endpoint reaches the public `opt` declaration, and prints
the path during the root build. This is a dependency audit, not a proof
premise. The existing `opt` theorem itself still has its original proof
through the earlier stronger helper and `fopt`.

### Complete proof details and manuscript correspondence

1. **Agreed statement changes:** the strict bounds on the weights and
   probabilities are replaced by the compact closure αᵢ ≥ 0 and
   pᵢ,qᶜᵢⱼ ≤ 1−ζ, and the conclusion explicitly supplies δ > 0.
   The manuscript file is preserved; these are the intended corrections
   specified in the conversation. All other hypotheses and all five
   conditions are retained.
2. **Remove zero weights:** restrict the index set to {i | αᵢ > 0}.
   The surviving weights still sum to one. All weighted matrix sums
   are unchanged because every deleted row or column has zero weight.
   Mathlib's `Finset.sum_congr_set`, `Fintype.sum_equiv`, and
   `Fintype.equivFin` justify the restriction and reindexing needed to
   apply the public `opt` theorem.
3. **Convert mass inequalities to equalities:** for each diagonal index,
   divide pᵢ, qᴮᵢᵢ, qᴳᵢᵢ by their sum; for each off-diagonal pair,
   divide qᴮᵢⱼ, qᴳᵢⱼ by their sum. All denominators are at least one.
   The new probabilities stay nonnegative and strictly below one and
   the required sums become one. Applying `opt` after positive-support
   restriction gives an outcome for the reduced data. Monotonicity of
   −log(1−t), square root, and the weighted costs transfers that outcome
   back to the original data. Symmetry is not needed for `opt`, so no
   symmetry condition is required by these reduction lemmas.
4. **Make compactness concrete:** for fixed k, form the compact product
   box of weights in [0,1] and probabilities in [0,1−ζ]. The bound
   αᵢ ≤ 1 follows from normalization and nonnegativity. The set `Bad`
   imposes normalization and conditions (c)–(e); it is closed in this
   compact box, hence compact. Logarithm continuity is valid even on
   the boundary because 1−pᵢ and 1−qᶜᵢⱼ are at least ζ > 0.
5. **A positive compact minimum gives the tolerance:** define
   D = ∑ᵢ max(1−pᵢ−qᴮᵢᵢ−qᴳᵢᵢ,0)
   + ∑ᵢ≠ⱼ max(1−qᴮᵢⱼ−qᴳᵢⱼ,0).
   This is continuous and nonnegative. It is strictly positive on `Bad`:
   otherwise all mass sums are at least one, and the reduction to `opt`
   contradicts the gap ζ in (c)–(e). If `Bad` is nonempty, its minimum
   m is positive. Choose δ = m/(k+k²+1). Conditions (a)–(b) would give
   D ≤ (k+k²)δ < m, a contradiction. If `Bad` is empty, choose δ = 1.
   This is an explicit implementation of the manuscript's compactness
   argument; it uses a minimum rather than a convergent subsequence.
6. **Uniformity in dimension:** there are finitely many k between zero
   and floor(1/ζ). Choose the least of their positive tolerances, using
   Mathlib's `Finset.exists_min_image`. The final statement restricts
   to the positive dimensions required by the manuscript. The resulting
   δ depends only on ζ, as required.
7. **No additional mathematical assumption:** the compactness proof in
   fact works without matrix symmetry. The public endpoint still
   includes the manuscript's symmetry hypotheses. There are no numerical
   computations or additional analytic estimates in this corollary.

Mathlib supplies compactness of closed real intervals, finite products
and function spaces, closedness of equalities and inequalities,
continuity of logarithm/square root/finite sums/max, and the extreme-value
result `IsCompact.exists_isMinOn`. These results are reused directly.
The only new first-party files are `OptApprox/Reduction.lean`,
`OptApprox/Compactness.lean`, `OptApprox.lean`, and the small dependency
audit module. No further external library is added.

The root module includes `#print axioms HadwigerRamsey.optapprox`.
Its only foundational dependencies are `propext`, `Classical.choice`,
and `Quot.sound`. The source guard and full build cover the new files.

## Migration to Lean 4.33.0

The project and GitHub workflow now use Lean 4.33.0 and Mathlib v4.33.0
(commit `db584cd6d46c92f209a44c0f1c829460d327499d`). Lake regenerated
`lake-manifest.json` for this release, including its transitive dependencies.
GitHub Actions explicitly prints the selected Lean version before checking
all proofs.

Theorem 1.4's endpoint remains `HadwigerRamsey.thomasonlower` in
`HadwigerRamsey/ThomasonLower.lean`. Its full declaration, including all
quantifiers, independence/measurability hypotheses, the condition L > epsilon,
and the real-valued probability conclusion, is unchanged from the previous
version and agrees with the October 31 manuscript. The proof and its supporting
`Probability.lean` and `Finite.lean` use Mathlib's renamed `probReal_univ`
in place of `measureReal_univ_eq_one`. There is no change to the mathematical
argument, and no new hypothesis, unproved assumption, or numerical evaluation
is introduced into Theorem 1.4.

The rest of the existing project is also migrated so that the shared toolchain
continues to support the earlier completed proofs. The cubic-sum proof makes
its addition inequality explicit for the new elaborator, and the derivative
proofs use `convert!` to unfold equivalent algebra instances. The vendored LeanCert
subset adapts renamed imports/casts, the smoothness interface, and the generalized
Taylor theorem; its README records these edits. The interval algorithms and
certificate values are unchanged. Expression evaluation and the convex minimum
argument use explicit definitional conversions in `FOpt/Envelope.lean`.
The dependency audit explicitly requests theorem bodies with
`ConstantInfo.value? (allowOpaque := true)`, as required by Lean 4.33's API;
it still checks the actual proof-expression path from `optapprox` to `opt`.

The first migration started from `main` and preserved the unfinished
Theorem 1.5 development separately on `codex/thomasonupper`. That branch
now also incorporates the upgrade for its existing checked ingredients.
That migration was limited to existing ingredients; the theorem has since
been completed as described below.

Validation on the migration: the full Lean 4.33 build passed (8737 jobs),
the source guard passed for all 32 Lean source files, and the dependency audit
confirmed the path from `optapprox` to public `opt`. The root axiom reports for
all completed endpoints contain only `propext`, `Classical.choice`, and
`Quot.sound`. The five public endpoint declarations were compared against the
previous version and are unchanged.

## Theorem 1.5 (`thomasonupper`): complete

**Theorem 1.5 is proved in Lean.** The public endpoint is
`HadwigerRamsey.thomasonupper` in `HadwigerRamsey/ThomasonUpper.lean`;
its proof is `ThomasonUpper.thomasonupper` in `ThomasonUpper/Final.lean`.
The October 31 TeX source remains ignored and is not part of the repository.
`ThomasonUpper/Progress.lean` collects the previously checked ingredients.

`ThomasonUpper.Statement` in `Definitions.lean` records the full statement.
It has exactly the manuscript's uniform quantifier order, real epsilon
greater than zero, vertex connectivity at least epsilon times the graph
order, class masses at least epsilon, and real lower bound
`n / sqrt(log n) * (sqrt(cappedLambda) - epsilon)`. The endpoint proves
this proposition with no additional assumptions.

The diagonal density is the number of edges in the induced class divided
by `choose(class size, 2)`. Off-diagonal density reuses Mathlib's
`SimpleGraph.edgeDensity`. The matrix is computed from the actual graph,
not supplied as independent numerical data. `cappedLambda` reuses the
existing `blockLambda`, so the sum is over ordered pairs and the cap is
exactly `min(p, 1-epsilon)`. Zero-denominator densities are totalized by
Lean's division convention, but `class_size_two` proves those cases do
not occur under the theorem's hypotheses once epsilon times n is at least
two. Vertices use `Fin n`, as for Theorem 1.4; the conclusion uses the
existing branch-set definition of the Hadwiger number.

Vertex connectivity is defined by the usual cut characterization, with
value zero on the empty or disconnected graph and n-1 for a complete
graph. `vertexConnectedAtLeast_iff` proves the exact maximum/cut
equivalence for positive n. It does not assume internally disjoint paths
in place of proving a Menger theorem. Its degree bound and the empty
large-epsilon regime are proved.

Checked components:

| Appendix step | Checked Lean declaration / module |
| --- | --- |
| Density bounds, symmetry, exact diagonal incidence conversion | `Density.lean` |
| Ordered block incidence sum equals twice the edge count | `sum_card_block_interedges` |
| Uniform upper bound on Lambda-star | `cappedLambda_le` |
| Connectivity implies the required degree-sum bound | `connectivity_mul_order_le_twice_edges` |
| Uniform lower bound epsilon(1-epsilon) on Lambda-star | `cappedLambda_lower`, `DensityLower.lean` |
| Positive class masses make diagonal densities well-defined | `class_size_two` |
| Greedy domination with the manuscript's exact logarithmic budget | `exists_dominating_set`, `Domination.lean` |
| Disjoint finite allocations from a reservoir | `disjoint_reservoir_selection`, `Selection.lean` |
| Allocation of all dominating sets M-a with epsilon/8 and epsilon R/4 constants | `reservoir_dominating_sets`, `ReservoirDomination.lean` |
| Discarding defective ordered pairs costs at most their number | `discard_defective_pairs`, `Deletion.lean` |
| Connected dominating cores turn a complete family into a clique minor | `cliqueMinor_of_complete_dominated`, `BranchSets.lean` |
| Uniform logarithm and product-mass perturbation bounds | `log_lipschitz`, `product_mass_stability`, `lambda_stability`, `Stability.lean` |
| Multiplicative accuracy gives the exact additive error outside the square root | `additive_accuracy` |
| Public finite vertex-Menger proof, with its full proof dependency subset | `Lax17Proofs.SimpleGraph.Menger.finite_vertex_menger_sharp`, `vendor/menger/` |
| Cut connectivity supplies disjoint set-to-set paths | `disjoint_paths_between_large_sets`, `Menger.lean` |
| Cut connectivity supplies internally disjoint paths, including adjacent endpoints | `internally_disjoint_paths`, `Menger.lean` |
| Appendix A.4, with positive connectivity and the same constants | `short_paths_vertexConnectivity`, `short_paths`, `Menger.lean`; counting in `ShortPaths.lean` |
| Greedily choose globally disjoint interiors from large candidate families | `exists_path_avoiding`, `allocate_path_interiors`, `PathAllocation.lean` |
| Appendix A.2: actual vertex-deletion stability, including diagonal densities and Lambda | `vertex_deletion_stability`, `DensityDeletion.lean` |
| Positive integer rounding with exact total and coordinate error at most 1/ell | `positive_rounded_masses`, `Rounding.lean` |
| Exact-multiple class trimming, positive common multiplicity, and uniform deletion bound | `rounded_class_trimming`, `Trimming.lean` |
| Regularized logarithmic weights: loss at most tau/a and uniform perturbation stability | `regularizedLambda_error`, `regularizedLambda_stability`, `Regularization.lean` |
| Appendix A.5 with the exact sampling rate, path length, reservoir sizes, and surviving-path threshold | `exists_reservoirs`, `ReservoirExistence.lean` |
| Independent path-survival events and Hoeffding event-count bounds | `IndependentBlocks.lean`, `Concentration.lean`, `ReservoirSampling.lean` |
| The three failure probabilities have sum below one uniformly for large n | `reservoir_failure_eventually_lt_one`, `ReservoirAsymptotic.lean` |
| Disjoint connected cores and the finite final clique-minor construction | `connected_reservoir_cores`, `cliqueMinor_of_reservoirs`, `ConnectedCores.lean`, `FiniteAssembly.lean` |
| Uniform reservoirs-first conversion of any admissible complete family into a minor | `reservoirs_complete_family_to_minor`, `FiniteAssembly.lean` |
| Both allocation budgets with the manuscript's actual logarithmic ceiling | `eventually_reservoir_allocation_budgets`, `AllocationBudgets.lean` |
| Exact floor counts in a capped spanning subgraph and uniform entropy rounding error | `exists_capped_subgraph_entropy`, `EdgeSelection.lean`, `Capping.lean` |
| A.1 nonneighbor averages, tau <= rho <= 1, and equation rho-geomean, including diagonal blocks | `rho_bounds`, `rho_geomean_bound`, `NonneighborWeights.lean` |
| A.1 sorted class blocks and exact equation block-max-product-all | `exists_sorted_nonneighbor_blocks`, `sorted_nonneighbor_max_product`, `SortedBlocks.lean`, `BlockMaxProducts.lean`, `SortedNonneighbors.lean` |
| Random parts form an exact equal-size partition and preserve the block/class enumeration | `BlockPartitions.lean`, `ClassBlocks.lean` |
| Uniform single and paired images, across every block; exact second-part remaining-vertex factorization | `UniformPermutations.lean`, `PermutationPairs.lean`, `BlockSampling.lean` |
| A.1 random-part probability at most rho^ell and equation block-expectation | `random_part_nonneighbor_probability`, `expected_block_nonneighbors`, `BlockAMGM.lean`, `NonneighborSampling.lean` |
| Rejection and unacceptable-part probability, and simultaneous four-times-expectation bounds | `rejected_block_probability`, `unacceptable_probability`, `exists_simultaneous_four_bounds`, `FiniteExpectations.lean` |
| Exactly k ineligible final blocks, acceptability's missing-block count, and the 2*omega factor | `eligibleBlocks_card`, `acceptable_missing_blocks`, `acceptable_pair_product_bound`, `SelectedBlocks.lean` |
| Full appendix A.1 with its exact P, part-count bounds, and complete-equipartition conclusion | `multitype_complete_equipartition`, `MultitypeFinite.lean`, `FiniteBlockTheorem.lean` |
| Expected ordered defect count, simultaneous outcome, endpoint deletion, and balanced extension | `RandomEquipartition.lean`, `CompleteEquipartition.lean`, `BalancedExtension.lean` |
| Exact finite total-probability calculation for the second random part | `ConditionalBlocks.lean`, `FiniteProbabilityFibers.lean`, `BlockNonneighbors.lean` |
| Equipartition part sizes lie between floor(n/m) and floor(n/m)+1 | `IsCompleteEquipartition.card_part_bounds`, `CompleteEquipartition.lean` |
| Exact log P formula, rounded quadratic margin, and uniform probability decay | `log_partitionFailure`, `rounded_quadratic_entropy_margin`, `eventually_partitionFailure_small`, `PartitionFailure.lean`, `PartitionFailureAsymptotic.lean` |
| Uniform at-least-(1-eta)*s parts for exact-multiple classes under the entropy margin, explicitly using A.1 | `multitype_many_parts_of_entropy_margin`, `MultitypeAsymptotic.lean` |
| Uniform auxiliary constants satisfying both strict gain/ratio inequalities and all three cost bounds in A.3 | `exists_multitype_asymptotic_parameters`, `AsymptoticParameters.lean` |
| Exact transport of deletion data to an actual graph on Fin (n-|Z|) | `Restriction.lean`, `restrictedLambda` |
| Uniform rounded scale, entropy error, and part count/size comparisons | `RoundedScale.lean`, `TrimmedEntropy.lean`, `AsymptoticFiniteBounds.lean` |
| Uniform complete-family consequence of A.3, explicitly using A.1 | `asymptotic_complete_family`, `AsymptoticFamily.lean` |
| Capping followed by reservoir deletion, with exact total entropy error | `exists_capped_restriction`, `CappedRestriction.lean` |
| Final uniform cutoffs, logarithmic order comparison, and additive accuracy | `FinalEventually.lean`, `FinalScale.lean` |
| Theorem 1.5 with the exact target statement | `HadwigerRamsey.thomasonupper`, `ThomasonUpper.lean`, `Final.lean` |

All ingredients needed for the target theorem are proved and assembled.
`asymptotic_complete_family` proves the uniform complete-family consequence
of A.3 from the actual rounded and trimmed graph parameters, explicitly
using A.1. It returns pairwise disjoint nonempty mutually joined parts
with the required count and size bounds, without requiring them to cover
the discarded vertices. This is all the final minor construction uses;
see difference 35 below. The final theorem caps the graph, removes the
reservoirs, applies this result, and converts the family into a clique minor.
All size cutoffs and approximation errors are uniform over the graph,
number of classes, and partition, depending only on epsilon.

Mathlib reuse includes induced-graph connectedness, connected unions and
walk supports, interedge counts, rational edge densities, the handshaking
lemma, the maximum possible edge count, finite fiber sums, and logarithm
inequalities. The reservoir argument now reuses Mathlib's independent
product measures, bounded-variable sub-Gaussian theorem, and Hoeffding
inequality. The A.1 ingredients additionally reuse Mathlib's sorted finite
orders, permutation decomposition and finite permutation-extension theorem,
uniform probability mass functions, and finite expectation linearity and
averaging principles. No new concentration inequality is assumed.

The literature search identified Thomason's *The Extremal Function for
Complete Minors* (2001), cited in the manuscript as MR1814910. No ready
Lean formalization of its complete-equipartition or dense-minor theorem
was located. A public finite vertex-Menger proof was located in
[Edouard Bonnet's polynomial-grid-minor-theorem project](https://github.com/EdouardBonnet/polynomial-grid-minor-theorem/blob/69d1714f3daa5ac49924b99950b4f4e283107cbe/proofs/Lax17Proofs/Source/Menger.lean).
That snapshot uses Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, now matching this project's
Lean/Mathlib version. The earlier temporary trial under 4.24 exposed missing
newer walk/list APIs. The four-file proof dependency subset is now vendored
unchanged under `vendor/menger/`, with its Apache 2.0 license and provenance.
The public theorem is used directly, and its kernel dependency report is
included in the root build. The upstream concept/contract files are not
imported. The local bridge derives internally disjoint endpoint paths from
the public set-to-set theorem and this project's cut definition of connectivity.

Logical correspondence and every change from the manuscript argument:

1. No hypothesis or conclusion of Theorem 1.5 has been changed. The
   endpoint proves the original target proposition. Changes to intermediate
   statements and arguments are recorded individually below.
2. The standalone domination lemma explicitly assumes both finite sides
   are nonempty. Those qualifications make the manuscript's logarithm
   and greedy choices meaningful. In the actual reservoir allocation,
   nonemptiness of the unused reservoir is proved from the positive
   remaining neighbor bound; complete-equipartition parts are nonempty.
   Thus this does not strengthen Theorem 1.5.
3. Domination is proved for a finite relation rather than a bundled
   bipartite graph, by the same double-counting and greedy iteration.
4. Analytic stability is expressed with the total absolute change in the
   class masses. The manuscript's maximum-coordinate estimate follows
   after the bounded-number-of-classes argument. This is now assembled
   with the graph-deletion estimates and the uniform asymptotic application.
5. The final connected-core lemma is slightly more general than the
   appendix: any disjoint connected dominating enlargements suffice.
   It preserves the same branch-set argument. No new assertion about
   finding those enlargements is assumed to establish Theorem 1.5.
6. Appendix A.4 explicitly assumes positive connectivity, as already
   authorized. Its parameter `k` may be any positive lower bound on the
   vertex connectivity, so the manuscript's value follows by taking
   `k = vertexConnectivity G`. The path count is written `k ≤ 2 * Q.card`,
   which is exactly the claimed real inequality `Q.card ≥ k/2`.
   `short_paths_vertexConnectivity` also states that specialization explicitly,
   using the manuscript's real-valued path-count inequality.
7. The cited Menger step is expanded using the existing public proof.
   For nonadjacent endpoints, a neighborhood packing gives `k` paths.
   For adjacent endpoints, it gives `k-1` paths with nonempty interiors,
   and the direct edge supplies the additional path. These details do not
   change the manuscript's argument or conclusion.
8. The counting proof uses the weaker bound of `n` on the total number
   of internal vertices, rather than `n-2`. This suffices for exactly the
   same bound `2n/k+1`. Lean filters the finite path family into short
   and long paths and compares their total numbers of internal vertices.
9. The final greedy path-allocation argument is stated for any finite
   list of requested distinct endpoint pairs. A candidate family for each
   request has more than `number_of_requests * (H-1)` internally disjoint
   paths, each of length at most `H` with interior in `C`. This is exactly
   the finite counting condition used in the appendix, abstracted from
   the consecutive-pair lists in the sets `M_a`. The reservoir existence,
   the asymptotic inequality ensuring that condition, and the construction
   of the connected cores are not assumed proved by this lemma.
10. Appendix A.2 now has a complete uniform endpoint for every `a > 0`.
    One possible explicit choice is
    `C = 2 + 8/a + 16/a^2 + 4*abs(log(2/a))/a` and
    `N = ceil(4/a) + 1`. Its entropy conclusion assumes `C*delta <= a/2`,
    an explicit version of the manuscript's sufficiently-small-delta
    qualification. The mass and density estimates hold throughout the
    original range `0 <= delta < a/2`. Although intermediate helpers
    assume `a <= 1`, the uniform endpoint derives this from the nonempty
    graph and class-size hypotheses; it is not a new hypothesis.
11. A.2 uses Mathlib's existing relation-density perturbation bound instead
    of reproducing the manuscript's edge-loss computation. A diagonal
    block is represented on ordered distinct vertex pairs; the numerator
    and denominator both double, so its density is exactly the original
    unordered-pair density. This yields the explicit stronger bounds
    `2*delta` for each mass change and `8*delta/a` for each density change.
    Surviving-class densities are computed directly in the original
    graph on the surviving classes. `deletedClassMass_eq_induced` and
    `deletedBlockDensity_eq_induced` prove equality with the actual class
    masses and densities in the induced graph `G-Z`, including the
    diagonal convention. Their complementary densities are written as `1-p`.
12. The A.3 rounding proof floors all scaled weights and adds one to an
    arbitrary subset of coordinates of the necessary size. The sum is
    exactly `ell`; each scaled coordinate changes by at most one.
    Positivity is proved under `a*ell >= 1`. This is the manuscript's
    rounding-remainder construction with an explicit largeness condition.
13. The A.3 trimming construction uses the same minimum of integer
    quotients and subsets of size `s*m_i`. Its uniform finite deletion
    bound is `n/(a*ell) + ell`, or fraction `1/(a*ell) + ell/n`.
    The combined endpoint assumes `a*ell >= 2` and `4*ell <= n` to
    guarantee `s > 0`. These conditions and the vanishing deletion
    fraction for the manuscript's eventual choice of `ell` are now
    proved uniformly in `eventually_rounded_scale` and used in
    `asymptotic_complete_family`.
14. The regularization estimates use the same function
    `-log(min(1,q+tau))`. Mathlib's bound for the minimum function and the
    existing logarithmic stability theorem replace the manuscript's
    informal Lipschitz argument. They allow any `tau >= 0`, a harmless
    generalization of the manuscript's `0 < tau < 1`; the loss bound
    remains exactly `tau/a`. They do not assert the probabilistic
    complete-equipartition result by themselves; the assembled
    `asymptotic_complete_family` now explicitly applies A.1.
15. A.5 uses exactly the manuscript's independent three-label experiment,
    with probabilities `r`, `r`, and `1-2*r`. Mathlib's Hoeffding inequality
    replaces the quoted multiplicative Chernoff bounds. The resulting
    total failure bound is
    `2*exp(-2*r^2*n) + n*exp(-c*r^2*n/2)`
    `+ n^2*exp(-c*n*(r^(H-1))^2/4)`.
    These exponents differ from the manuscript, but all three conclusions,
    including `r = 1/log(log n)`, `H = ceil(2/c)+1`, and
    `T = c*n*r^(H-1)/4`, are unchanged. The order threshold still depends
    only on `c`.
16. Path-survival probabilities may differ with path length. Their events
    are proved independent from disjoint interiors, and each probability
    is bounded below by `r^(H-1)`. Hoeffding is applied to these independent,
    not necessarily identically distributed indicators. For every fixed
    positive coefficient and fixed power, the asymptotic proof bounds the
    exponential tail by `n^-4`; this is sufficient for the same union
    bounds. It uses `log(log n) <= log n` and Mathlib's existing result
    that powers dominate logarithmic powers, rather than the manuscript's
    informal growth comparison.
17. Each nonempty `M_a` is connected by a star from one selected root,
    rather than by consecutive-pair paths in a list. There are exactly
    `|M_a|-1` requests, so the manuscript's `m*L` path budget still applies.
    The root contributes a length-zero walk when expressing the connected
    core as a union of walk supports; it consumes no reservoir vertices.
    Nonemptiness of `M_a` is derived from its domination of nonempty `W_a`.
18. The finite final assembly states its complete family, reservoir
    separation, and two allocation budgets explicitly. These are the
    same inputs used in the appendix. The allocation-budget theorem
    proves both budgets uniformly from `m <= C*n/sqrt(log n)` and
    `K <= C*sqrt(log n)`, with the exact ceiling-logarithm formula for `L`.
    It assumes `K >= 1` and `H >= 1`, as satisfied by the manuscript's
    parameters, and allows a larger uniform order threshold.
    `reservoirs_complete_family_to_minor` combines these results: it
    chooses `C,D` first, then handles every complete family outside them
    with the stated size bounds. Thus reservoir existence and both
    allocation budgets are discharged rather than assumed by that endpoint.
19. Edge thinning is indexed by unordered pairs of class labels, so each
    undirected edge is selected once. The resulting graph is a spanning
    subgraph of `G`; the chosen counts are exactly the manuscript's
    floors, with denominator `n_i*n_j` off the diagonal and `choose(n_i,2)`
    on the diagonal. The entropy error is explicitly at most
    `4/(epsilon*a^2*n^2)` when each class has size at least `a*n` and
    `a*n >= 2`. This gives the manuscript's uniform vanishing error;
    it does not assume the thinned graph retains connectivity.
20. The A.1 preliminary estimates use the complement graph to encode
    nonneighbors distinct from the vertex itself. For diagonal blocks,
    Lean proves the upper bound needed later rather than recording the
    exact extra factor `(n_i-1)/n_i`. The logarithmic form of AM-GM follows
    from Mathlib's `log x <= x-1`, and exponentiating gives the original
    product-form `rho-geomean` inequality with the same `ell_j/ell` weights.
    These estimates now feed the sorted-block and random-sampling results
    below and the full finite complete-equipartition conclusion.

21. Sorting breaks equal rho-values by the existing vertex order. A block's
    final sorted vertex attains its maximum, so this is the manuscript's
    theta, not a different bound. The block-shift calculation uses sums of
    logarithms and then exponentiates. Its product form keeps precisely
    the ordered double product with powers ell_i*ell_j and the factor
    tau^(-ell*(ell-m)); no density or factor-two convention changes.
22. Random orderings are sampled uniformly from the finite space of all
    block-permutation functions. This is exactly independent uniform
    orderings in each block. Mathlib's permutation decomposition and
    extension of an injective pair supply the uniform marginal laws.
    Instead of invoking conditional probability, Lean proves the exact
    joint identity: the fixed first vector contributes (1/s)^ell and the
    second vector contributes the product of |T minus x|/(s-1). Thus the
    exclusion of each first image is explicit; distinct positions in one
    block are never treated as independent.
23. The random-part AM-GM estimate goes directly to the regularized
    nonneighbor fractions, combining the manuscript's last two
    inequalities into one. Zero block proportions are handled before
    applying the logarithmic estimate. The result is the same rho^ell
    bound and the same |B|*theta^ell block expectation. The helpers make
    ell > 0 explicit, as used for nonempty classes in the application.
24. Expectations use Mathlib's finite uniform average, with a proved
    identity to the uniform event probability. The rejection estimate is
    Markov's inequality in its strict-threshold form. Counting eligible
    blocks omits exactly one block per class and gives exactly
    ell-m <= k+phi*ell. The second-part product estimate uses s/(s-1) <= 2
    and pads (2*omega)^m to (2*omega)^ell, as in the manuscript.
    `acceptable_pair_product_bound` combines these numerical inequalities
    with the sorted-maxima estimate to obtain exactly the expression P;
    its graph-dependent inputs and the expected defect count are now
    assembled in `multitype_complete_equipartition`.
25. The helper choosing simultaneous U,Z bounds uses the expected value
    of U/A+Z/B, which is at most 2, and Mathlib's finite averaging
    principle. It returns the same U <= 4*A and Z <= 4*B conclusion as
    the manuscript's two Markov bounds and union bound. This alternative
    choice argument is now connected to the full A.1 defect-count
    construction and complete-equipartition conclusion.

26. The full A.1 statement explicitly assumes k > 0 and returns at least
    one nonempty part. With ell_i >= 1 and s >= 2, the exact class sizes
    then force a nonempty graph. This makes explicit the intended
    nonempty partition convention: the k = 0 empty-graph case would need
    a separate convention for a partition into positive parts. Theorem
    1.5 is applied at positive large n, where a vertex-to-class map forces
    k > 0. The expression P and both part-count bounds are unchanged.
27. The accepted-pair calculation sums exact joint probabilities over
    all possible first vectors. It bounds the event that both parts are
    acceptable and have no joining edge by the larger event that the
    first is acceptable and the second lies in its common nonneighbors,
    exactly as used in the manuscript's calculation. Z counts ordered
    distinct acceptable pairs. Lean uses E Z <= s^2*P, rather than the
    manuscript's strict E Z < s^2*P; this weaker estimate gives the same
    final deletion bound 4*s^2*P.
28. Balanced redistribution preserves every surviving core. If there
    are at least as many leftover vertices as surviving parts, Lean
    reuses Mathlib's existing equipartition theorem for the leftovers.
    Otherwise it injects the leftover vertices into the part indices,
    adding zero or one vertex to each. This spells out the manuscript's
    redistribution instruction without changing its conclusion. The
    resulting indexed parts have sizes differing by at most one; Mathlib's
    equitable-family estimate also gives floor(n/m) <= |W_i| <= floor(n/m)+1.
29. The A.3 preliminary estimate keeps P exactly as defined in A.1. Its
    logarithm is L*log(2*omega) - L*(k+phi*L)*log(tau)
    - L^2*Lambda_reg, with the exact weights ell_i/L. The uniform-decay
    helper assumes L <= C*sqrt(log n), k <= K, and a quadratic margin
    L^2*(Lambda_reg+phi*log(tau)) >= (1+delta)*log n. Mathlib's growth
    of sqrt(log n) then absorbs the linear term and proves
    P <= n^(-(1+delta/2)) uniformly. Obtaining that margin from the actual
    rounded graph parameters is now completed in `AsymptoticFamily.lean`.
    The finite helper `rounded_quadratic_entropy_margin` proves that
    L >= (1+gamma)*sqrt(log(n)/Lambda), R >= (1-2*xi)*Lambda,
    phi*log(1/tau) <= xi*Lambda, and
    (1+gamma)^2*(1-3*xi) >= 1+delta imply precisely that margin.
    This retains the manuscript's factor 1-3*xi. Establishing R's bound
    for the actual trimmed graph and the final rounding/trimming part-count
    comparisons are now proved in `AsymptoticFamily.lean`.
    `eventually_defective_pair_loss_small` proves 4*s*P <= eta/2
    uniformly from s <= n and P <= n^(-(1+xi)). Together with
    4/(omega*phi) <= eta/2, the theorem
    `multitype_many_parts_of_entropy_margin` explicitly applies A.1 and
    returns at least (1-eta)*s parts. It still assumes exact-multiple
    classes and the quadratic margin, so it is a checked intermediate
    consequence used by the assembled complete-family endpoint below.

30. The unspecified small/large constants in the start of A.3 are chosen
    explicitly and uniformly. Lean takes gamma = min(eta,1)/8,
    xi = gamma/(12*(1+gamma)^2), tau = min(1/2,a*xi*lambda/2),
    phi = min(1/2,xi*lambda/(2*(log(1/tau)+1))), and
    omega = max(1,4/(xi*phi)). It proves both manuscript inequalities
    (1-2*xi)/(1+gamma) > 1-eta and
    (1+gamma)^2*(1-3*xi) > 1+2*xi, together with the three cost bounds.
    It also records phi < 1 and 3*xi <= 1, as satisfied by these choices
    and needed by the finite and quadratic-margin helpers. This supplies
    explicit witnesses for the manuscript's choices, without changing
    the assumptions a > 0, lambda > 0, eta > 0.

31. Actual induced graphs are reindexed by a finite equivalence with
    `Fin (n-|Z|)`. Injectivity proves that class cardinalities, diagonal
    unordered densities, off-diagonal densities, and entropy agree exactly
    with the earlier deletion definitions. No graph data or density matrix
    is replaced by independent numerical assumptions.
32. The ceiling scale is controlled uniformly for
    `lambda <= Lambda <= log(1/a)+1`. The harmless added one makes the
    upper-bound constant positive even at a = 1. Explicit fixed lower bounds
    on ell and upper bounds on ell/n discharge every rounding, positivity,
    trimming, and floor-error condition. Auxiliary helpers assume
    `a <= 1` and `0 < eta < 1`; the final application satisfies both.
33. The rounded, deleted, regularized entropy error is explicitly at most
    `tau/a + 16*delta/a^2 + 2*log(2/a)/(a*ell)`. The last two terms are each
    at most xi*lambda/2, and tau/a <= xi*lambda. Hence the same manuscript
    inequality `Lambda0_tau >= (1-2*xi)*Lambda` follows. The same
    `(1-3*xi)` quadratic margin then feeds the already proved A.1 estimate.
34. An ambient-order variant of the many-parts theorem allows the actual
    graph to have order N <= n while using log n in the scale and failure
    bound. Here n is the original order before the rounding deletion,
    exactly as in the manuscript A.3 calculation. The quantity P, weights,
    ordered double sums, and density conventions remain unchanged.
35. Instead of redistributing A.3's discarded vertices back into its parts,
    `asymptotic_complete_family` keeps the complete equipartition of the
    trimmed graph as a family in the original graph. It proves the same
    lower and upper part counts and the required upper part-size bound.
    Thus its standalone conclusion omits coverage and global balance on
    the original vertex set. Theorem 1.5 only uses a disjoint complete
    family outside the reservoirs, so these omissions require no change
    to its statement. The finite A.1 endpoint still has its full complete
    equipartition conclusion, including coverage and balance.
36. The final accuracy choice is
    `eta = min(1/4, epsilon/(8*(sqrt(log(1/epsilon)+1)+1)))`.
    Rather than introducing epsilon-prime and splitting off its >= 1 case,
    Lean bounds the total entropy error by `(epsilon/4)^2`, the deleted
    fraction by eta, and uses `4*eta*sqrt(B) <= epsilon`. A square-root
    inequality gives the required additive error directly. This changes
    the auxiliary constants and the final error-bookkeeping argument,
    not the theorem's error term, quantifiers, or uniformity.
37. The final proof explicitly compares the retained order N with n:
    N >= n/2, sqrt(log N) <= sqrt(log n) <= 2*sqrt(log N).
    A single larger size constant `2*C+2` handles both the integer ceiling
    on part sizes and the reservoir allocation theorem. Capping is used
    only to construct the complete family; connectivity is always that of
    the original G, where the final branch sets are connected. The case
    epsilon >= 1 is excluded by kappa(G) < n for positive n.

38. Lean selects the reservoirs in G before selecting the capped spanning
    subgraph H; the manuscript makes these independent choices in the
    opposite order. The reservoir theorem uses only G and its connectivity,
    while the capping theorem works uniformly for every eligible partition.
    Both required conclusions therefore hold together in either order.

The completed project passes `lake build` on Lean/Mathlib 4.33.0
(8807 jobs). The source guard passes for all 103 Lean source files.
The root build includes every earlier formalized result and reports that
`HadwigerRamsey.thomasonupper` depends only on `propext`,
`Classical.choice`, and `Quot.sound`. No theorem or unproved appendix
statement is assumed as an extra premise.

### Historical upgrade of the existing Theorem 1.5 ingredients to Lean 4.33.0

The progress branch incorporates the checked upgrade from `main` and uses
Lean/Mathlib 4.33.0. This update only ports the ingredients already present:
all 50 existing declaration headers and the target proposition are unchanged,
and no additional declaration is introduced.

Four proof scripts need compatibility edits: the connected-union call now
passes `.preconnected`, the filter-cardinality lemma is renamed to
`Finset.card_filter_add_card_filter_not`, a reflexive conditional is simplified
explicitly in the density proof, and the stability proof supplies both summands
of its final addition inequality explicitly. These edits change no mathematical
statement or argument. This paragraph records the earlier port only; the
subsequent work described above completes the theorem.

The full combined build passed on Lean 4.33.0 (8748 jobs), the source guard
passed for all 43 Lean files, and the root dependency reports use only
`propext`, `Classical.choice`, and `Quot.sound`.
