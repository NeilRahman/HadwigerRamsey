# Formalization status

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

Pinned Lean: `leanprover/lean4:v4.24.0`.
Pinned Mathlib: tag `v4.24.0`, commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
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

The original manuscript and existing counterexample notes are preserved
without edits. The mathematical correspondence above is documented for
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
[Mathlib.Order.Partition.Finpartition](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Order/Partition/Finpartition.lean)
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
- [Mathlib finite Jensen](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Analysis/Convex/Jensen.lean):
  `convexOn_exp.map_sum_le` is reused directly.
- [Mathlib independence](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Probability/Independence/Basic.lean):
  the proof reuses `iIndepSet_iff` and
  `iIndepSet.indep_generateFrom_of_disjoint`, along with measurable
  generated events and the measure-of-intersection product identity.
- [Mathlib power/logarithm asymptotics](https://github.com/leanprover-community/mathlib4/blob/v4.24.0/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean):
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

All three manuscript endpoints are imported and their dependency reports
printed in `HadwigerRamsey.lean`. The source guard also checks vendored
Lean sources. The fopt endpoint requires only `propext`,
`Classical.choice`, and `Quot.sound`.
